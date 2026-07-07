(* This module implements occurrence analysis of the currently-being-defined constants and metavariables in the argument types of datatype constructors, in order to detect recursive datatypes.  In the future it should also be usable for checking strict positivity of recursive occurrences, by additionally tracking the positions in which occurrences appear (e.g. flipping polarity when the typechecker descends into the domain of a pi-type).

   The detection happens *during* typechecking, rather than by a separate traversal of checked terms afterwards: the typechecker records occurrences as it resolves constant references, creates holes, and refers to let-bound variables whose values contained occurrences.  A separate traversal could not be correct, since a checked constructor type contains only a variable reference when it mentions a let-bound value: the occurrences hide in the value of that variable, which lives outside the data node (or behind a metavariable, for case-tree lets). *)

(* The recursion status of a datatype (or, during checking, of a single constructor or the value of a let binding): either it definitely contains no occurrences of anything currently being defined, or it definitely contains one, or it is not yet known because of unsolved holes whose eventual solutions might contain occurrences.  In the unknown case we store the blocking metavariables, so that when they are solved, the verdicts recorded for their solutions can be chased at the point of use (just as evaluation of a term containing metavariables consults their definitions). *)
type recursion = [ `Nonrecursive | `Recursive | `Unknown of Meta.WrapSet.t ]

(* When "linking" a marshaled term unpickled from a compiled file, the metavariables in an `Unknown verdict must have their file autonumbers replaced along with all the other metavariables occurring in terms (see Link).  (Compiled files can't contain unsolved holes, but an `Unknown verdict blocked on since-solved holes is never rewritten, so it can appear in a compiled file.) *)
let link_recursion : (Origin.File.t -> Origin.File.t) -> recursion -> recursion =
 fun f -> function
  | `Nonrecursive -> `Nonrecursive
  | `Recursive -> `Recursive
  | `Unknown ms -> `Unknown (Meta.WrapSet.map (fun (Meta.Wrap m) -> Meta.Wrap (Meta.remake f m)) ms)

let merge : recursion -> recursion -> recursion =
 fun x y ->
  match (x, y) with
  | `Recursive, _ | _, `Recursive -> `Recursive
  | `Unknown s, `Unknown t -> `Unknown (Meta.WrapSet.union s t)
  | (`Unknown _ as u), `Nonrecursive | `Nonrecursive, (`Unknown _ as u) -> u
  | `Nonrecursive, `Nonrecursive -> `Nonrecursive

(* The set of constants currently being defined: those of the current "def" block, or, when solving a hole, those that were being defined when the hole was created. *)
module BeingDefined = Algaeff.Reader.Make (struct
  type t = unit Constant.Map.t
end)

let () =
  BeingDefined.register_printer (function `Read -> Some "unhandled Positivity.BeingDefined effect")

(* The collector is a stack of verdict accumulators for nested scopes.  A scope is opened around checking anything whose occurrences we want to know about: the argument telescope of each datatype constructor, and the value of each let or letrec binding.  Since the stack is mutable state confined to a dynamic extent, we implement it as a reader effect holding a mutable record. *)
type stack = { mutable frames : recursion list }

module Collector = Algaeff.Reader.Make (struct
  type t = stack
end)

let () =
  Collector.register_printer (function `Read -> Some "unhandled Positivity.Collector effect")

(* Install handlers for both effects.  This is done once at top level with an empty being-defined set; the callers that know a real being-defined set (checking a "def" block, or solving a hole) re-wrap with "run_beingdefined" below. *)
let run : type a. (unit -> a) -> a =
 fun f -> BeingDefined.run ~env:Constant.Map.empty @@ fun () -> Collector.run ~env:{ frames = [] } f

let run_beingdefined : type a. unit Constant.Map.t -> (unit -> a) -> a =
 fun beingdefined f -> BeingDefined.run ~env:beingdefined f

let beingdefined () = BeingDefined.read ()

(* Record a verdict into the innermost active scope, if any. *)
let record : recursion -> unit =
 fun v ->
  let s = Collector.read () in
  match s.frames with
  | [] -> ()
  | top :: rest -> s.frames <- merge v top :: rest

(* Called by the typechecker when it resolves a reference to a constant. *)
let record_const : Constant.t -> unit =
 fun c ->
  let s = Collector.read () in
  match s.frames with
  | [] -> ()
  | top :: rest ->
      if Constant.Map.mem c (BeingDefined.read ()) then s.frames <- merge `Recursive top :: rest

(* Called by the typechecker when it creates a hole. *)
let record_hole : type mode a b s. (mode, a, b, s) Meta.t -> unit =
 fun m -> record (`Unknown (Meta.WrapSet.singleton (Wrap m)))

(* Run a callback in a new scope, returning its result along with the verdict of that scope.  The verdict is also merged into the enclosing scope, since anything containing occurrences is itself something containing occurrences.  We pop the scope even if the callback raises (e.g. a fatal error that will be caught and recovered from by Reporter.try_with, as when accumulating errors in the constructors of a datatype), to keep the stack balanced. *)
let scope : type a. (unit -> a) -> a * recursion =
 fun f ->
  let s = Collector.read () in
  s.frames <- `Nonrecursive :: s.frames;
  let pop () =
    match s.frames with
    | v :: rest ->
        (match rest with
        | top :: rest -> s.frames <- merge v top :: rest
        | [] -> s.frames <- []);
        v
    | [] -> `Nonrecursive in
  match f () with
  | result -> (result, pop ())
  | exception e ->
      let _ = pop () in
      raise e
