(* This module should not be opened, but used qualified. *)

open Util
open Signatures
open Dimbwd
open Energy
open Origin

(* Metavariables, such as holes and unification variables.  Local generative definitions are also reperesented as metavariables.  A metavariable is identified by its class, an autonumber that's specific to the class, and its origin (file or interactive instant).  Since the autonumbers are specific to the class, we store them as arguments of the class, even though every metavariable has one. *)

module Identity = struct
  type t = [ `Hole of int | `Def of int * string * string option ]

  let compare : t -> t -> int = compare
end

(* A metavariable is also parametrized by its raw context length, its checked context length, and its energy (kinetic or potential), although these are not part of its identity. *)
type ('a, 'b, 's) t = {
  origin : Origin.t;
  identity : Identity.t;
  raw : 'a N.t;
  len : 'b Dbwd.t;
  energy : 's energy;
}

(* Make metavariables of each class. *)

(* Store autonumber counters for defined metavariables, for both files and instants. *)
let def_counters = Versioned.make ~default:(fun _ -> 0) ~inherit_values:false

(* Create a new defined constant in the current execution location (file or interactive instant). *)
let make_def : type a b s. string -> string option -> a N.t -> b Dbwd.t -> s energy -> (a, b, s) t =
 fun sort name raw len energy ->
  let origin = Origin.current () in
  let number = Versioned.get def_counters in
  Versioned.set def_counters (number + 1);
  let identity = `Def (number, sort, name) in
  { origin; identity; raw; len; energy }

(* We just use one global hole counter, so that a hole can be represented by a single number to communicate with the user and ProofGeneral.  But to make up for that, we have to remember the origin of each hole as a function of its global number.  And then, since the next number is just the length of this array, we don't need a separate counter for hole autonumbers.  Note that this dynarray never shrinks, so old holes that have gone away are still here.  There wouldn't be any easy way to do that, since solving an old hole can create new holes that have to be at the end of the array, so the origins don't appear here in order. *)
let hole_origins : Origin.t Dynarray.t = Dynarray.create ()

let make_hole : type a b s. a N.t -> b Dbwd.t -> s energy -> (a, b, s) t =
 fun raw len energy ->
  let origin = Origin.current () in
  let number = Dynarray.length hole_origins in
  Dynarray.add_last hole_origins origin;
  let identity = `Hole number in
  { origin; identity; raw; len; energy }

(* Re-make (link) a metavariable when loading a compiled version from disk. *)
let remake : type a b s. (File.t -> File.t) -> (a, b, s) t -> (a, b, s) t =
 fun f m ->
  match m.origin with
  | Top -> raise (Failure "can't remake built-in metavariable")
  | File file -> { m with origin = File (f file) }
  | Instant _ -> raise (Failure "can't remake interactive metavariable")

(* Printable names. *)
let name : type a b s. (a, b, s) t -> string =
 fun x ->
  match x.identity with
  | `Hole number ->
      (* We don't need to include the origin here, since holes are sequentially numbered globally rather than by origin. *)
      Printf.sprintf "?%d" number
  | `Def (number, sort, None) -> Printf.sprintf "_%s.%s.%d" sort (Origin.to_string x.origin) number
  | `Def (number, sort, Some name) ->
      Printf.sprintf "_%s.%s.%d.%s" sort (Origin.to_string x.origin) number name

let origin : type a b s. (a, b, s) t -> Origin.t = fun m -> m.origin

(* Compare two metavariables for equality, returning equality of their lengths and energies. *)
let compare : type a1 b1 s1 a2 b2 s2.
    (a1, b1, s1) t -> (a2, b2, s2) t -> (a1 * b1 * s1, a2 * b2 * s2) Eq.compare =
 fun x y ->
  match
    ( x.origin = y.origin,
      x.identity = y.identity,
      N.compare x.raw y.raw,
      Dbwd.compare x.len y.len,
      Energy.compare x.energy y.energy )
  with
  | true, true, Eq, Eq, Eq -> Eq
  | _ -> Neq

type wrapped = Wrap : ('a, 'b, 's) t -> wrapped

module Wrapped = struct
  type t = wrapped

  let compare : t -> t -> int = fun (Wrap x) (Wrap y) -> Identity.compare x.identity y.identity
end

module WrapSet = Set.Make (Wrapped)

(* Representation of holes for interacting with ProofGeneral. *)
let hole_number : type a b s. (a, b, s) t -> int =
 fun m ->
  match m.identity with
  | `Hole number -> number
  | _ -> raise (Failure "not an interactive hole")

(* A metavariable table, like a constant table, is MUTABLE and versioned, and can store anything.  It is also intrinsically well-typed, with values that can be parametrized by the raw length, checked length, and energy of the metavariable. *)

module IdMap = Map.Make (Identity)

module Table = struct
  type ('a, 'b, 's) key = ('a, 'b, 's) t

  module Make (F : Fam4) = struct
    type _ entry = Entry : ('a, 'b, 's) key * ('x, 'a, 'b, 's) F.t -> 'x entry
    type 'x t = 'x entry IdMap.t Versioned.t

    let make () = Versioned.make ~default:(fun () -> IdMap.empty) ~inherit_values:false

    let find_opt : type x a b s. (a, b, s) key -> x t -> (x, a, b, s) F.t option =
     fun key m ->
      (* Apparently we can't use Monad.Ops(Monad.Maybe) here because the type doesn't get sufficiently refined. *)
      match Versioned.get_at m key.origin with
      | Some m -> (
          match IdMap.find_opt key.identity m with
          | None -> None
          | Some (Entry (key', value)) -> (
              match compare key key' with
              | Eq -> Some value
              | Neq -> raise (Failure "Meta.Map.find_opt")))
      | None -> None

    let find_hole_opt : type x. int -> x t -> x entry option =
     fun i m ->
      try
        let c = Dynarray.get hole_origins i in
        match Versioned.get_at m c with
        | Some m -> IdMap.find_opt (`Hole i) m
        | None -> None
      with Invalid_argument _ -> None

    let update : type x a b s.
        (a, b, s) key -> ((x, a, b, s) F.t option -> (x, a, b, s) F.t option) -> x t -> unit =
     fun key f m ->
      if key.origin = Origin.current () then
        let a = Option.value ~default:IdMap.empty (Versioned.get_at m key.origin) in
        let newa =
          IdMap.update key.identity
            (function
              | None -> (
                  match f None with
                  | None -> None
                  | Some fx -> Some (Entry (key, fx)))
              | Some (Entry (key', value)) -> (
                  match compare key key' with
                  | Eq -> (
                      match f (Some value) with
                      | None -> None
                      | Some fx -> Some (Entry (key, fx)))
                  | Neq -> raise (Failure "Meta.Map.update")))
            a in
        Versioned.set m newa
      else raise (Failure "Meta.Table: can only update/add to the current origin")

    let add : type x a b s. (a, b, s) key -> (x, a, b, s) F.t -> x t -> unit =
     fun key value m -> update key (fun _ -> Some value) m

    let _remove : type x a b s. (a, b, s) key -> x t -> unit =
     fun key m -> update key (fun _ -> None) m

    type ('x, 'acc) folder = {
      fold : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> 'acc -> 'acc;
    }

    let fold : type x acc. (x, acc) folder -> x t -> acc -> acc =
     fun f m acc ->
      let go acc m = IdMap.fold (fun _ (Entry (key, value)) acc -> f.fold key value acc) m acc in
      Versioned.fold m go acc

    let fold_current : type x acc. (x, acc) folder -> x t -> acc -> acc =
     fun f m acc ->
      IdMap.fold (fun _ (Entry (key, value)) acc -> f.fold key value acc) (Versioned.get m) acc

    type 'x origin_entry = 'x entry IdMap.t option

    let find_file (file : File.t) (m : 'a t) = Versioned.get_at m (File file)

    let add_file file x m =
      match x with
      | Some x -> Versioned.set_file m file x
      | None -> ()

    let to_channel_origin : type x.
        Out_channel.t -> Origin.t -> x t -> Marshal.extern_flags list -> unit =
     fun chan origin m flags -> Marshal.to_channel chan (Versioned.get_at m origin) flags

    type 'x mapper = {
      map : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> ('x, 'a, 'b, 's) F.t;
    }

    let from_istream_origin : type x. Istream.t -> x mapper -> Origin.t -> x t -> x origin_entry =
     fun chan f origin m ->
      match (Istream.unmarshal chan : x origin_entry) with
      | Some n ->
          let fn = IdMap.map (fun (Entry (key, value)) -> Entry (key, f.map key value)) n in
          Option.bind (Versioned.set_at m origin fn) @@ fun () -> Some fn
      | None -> None
  end
end
