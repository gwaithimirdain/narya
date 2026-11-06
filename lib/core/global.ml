(* This module should not be opened, but used qualified. *)

open Bwd
open Util
open Modal
open Tctx
open Reporter
open Term
open Printable
open Origin

(* The global environment of constants and definition-local metavariables. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types.  *)
type 'mode definition_args = {
  mode : 'mode Mode.t;
  ty : ('mode, 'mode emp, kinetic) term;
  tm : [ `Axiom | `Defined of ('mode, 'mode emp, potential) term ];
  (* A parametric constant can have external degeneracies applied to it, while a nonparametric one can't.  A maybe-parametric one is one currently being typechecked which hasn't yet been concluded to be nonparametric. *)
  parametric : [ `Parametric | `Nonparametric | `Maybe_parametric ];
}

type definition = Definition : 'mode definition_args -> definition

(* The versioned global table of defined constants. *)
let constants : (definition, Code.t) Result.t Constant.Table.t = Constant.Table.make ()

(* Global metavariables have only a definition (or an error indicating that they can't be correctly accessed, such as if typechecking failed earlier). *)
module Metatable = Meta.Table.Make (struct
  type ('x, 'mode, 'a, 'b, 's) t = (('mode, 'a, 'b, 's) Metadef.t, Code.t) Result.t
end)

module Holetable = Meta.Table.Make (struct
  type ('x, 'mode, 'a, 'b, 's) t = ('mode, 'a, 'b, 's) Metadef.hole
end)

(* The versioned global tables for metavariables (including holes) and for special hole data. *)
let metas : unit Metatable.t = Metatable.make ()
let holes : unit Holetable.t = Holetable.make ()

(* Caches of evaluated values (e.g. the cache of evaluated constants in Norm) must be invalidated whenever the meaning of an existing constant or metavariable could change, since evaluation reads the global state.  (Additions of fresh constants and metavariables couldn't affect previously cached values, but we invalidate on them too, for safety; they are rare.)  Time-travel (undo and rewind) is not handled by these hooks; caches should be stored in an Origin.Versioned to deal with that. *)
let invalidators : (unit -> unit) list ref = ref []

(* Register a callback to be invoked whenever the global state of constants or metavariables is mutated, so that caches of evaluated values can be invalidated.  (Time-travel is not signaled by these callbacks; caches should be stored in an Origin.Versioned to deal with that.) *)
let register_invalidator f = invalidators := f :: !invalidators
let invalidate () = List.iter (fun f -> f ()) !invalidators

(* Invalidating wrappers around the primitive mutations of the constant and metavariable tables.  All modifications of those tables should go through these. *)
let consttable_add c v =
  invalidate ();
  Constant.Table.add c v constants

let metatable_add m v =
  invalidate ();
  Metatable.add m v metas

(* Look up a constant. *)
let find_const c =
  match Constant.Table.find_opt c constants with
  | Some (Ok d) -> d
  | Some (Error e) -> fatal e
  | None -> fatal (Undefined_constant (PConstant c))

(* Similarly, look up a metavariable. *)
let find_meta m =
  match Metatable.find_opt m metas with
  | Some (Ok d) -> d
  | Some (Error e) -> fatal e
  | None -> fatal (Anomaly ("undefined metavariable: " ^ Meta.name m))

(* The name of a metavariable, using the owner and local name stored in its definition, if it has one. *)
let meta_name : type mode a b s.
    ?owner_name:(Constant.t -> string) -> (mode, a, b, s) Meta.t -> string =
 fun ?owner_name m ->
  match Metatable.find_opt m metas with
  | Some (Ok { owner; local; _ }) -> Meta.name ?owner_name ?owner ?local m
  | _ -> Meta.name ?owner_name m

(* Run a callback with the same owner as a given metavariable, such as a hole being solved, so that the metavariables created by the callback have that owner. *)
let with_owner_of : type mode a b s x. (mode, a, b, s) Meta.t -> (unit -> x) -> x =
 fun m f -> Meta.with_owner_opt (find_meta m).owner f

(* Combine all the data for a hole, to return them when looked up. *)
type find_hole =
  | Found_hole : {
      meta : ('mode, 'a, 'b, 's) Meta.t;
      instant : Instant.t;
      termctx : ('mode, 'a, 'b) termctx;
      ty : ('mode, 'b, kinetic) term;
      status : ('mode, 'b, 's) Status.status;
      vars : (string option, 'a) Bwv.t;
      li : No.interval;
      ri : No.interval;
      parametric : [ `Parametric | `Nonparametric ];
      beingdefined : unit Constant.Map.t;
    }
      -> find_hole

(* Subroutine for returning those data. *)
let return_hole : type mode a b s.
    (mode, a, b, s) Meta.t ->
    ((mode, a, b, s) Metadef.t, Code.t) Result.t ->
    (mode, a, b, s) Metadef.hole option ->
    find_hole option =
 fun meta def hole ->
  match (def, hole) with
  | Ok { tm = `Undefined; termctx; ty; _ }, Some { status; vars; li; ri; parametric; beingdefined }
    -> (
      match Meta.origin meta with
      | Instant instant ->
          Some
            (Found_hole
               { meta; instant; termctx; ty; status; vars; li; ri; parametric; beingdefined })
      | _ -> fatal (Anomaly "timeless hole"))
  | Error e, _ -> fatal e
  | _ -> None

let find_hole i =
  let open Monad.Ops (Monad.Maybe) in
  match
    let* (Hole (meta, def)) = Metatable.find_hole_opt i metas in
    let hole = Holetable.find_opt meta holes in
    return_hole meta def hole
  with
  | Some found -> found
  | None -> fatal (No_such_hole i)

let all_holes () =
  Metatable.fold
    {
      fold =
        (fun m v hs ->
          match return_hole m v (Holetable.find_opt m holes) with
          | Some h -> Bwd.Snoc (hs, h)
          | None -> hs);
    }
    metas Emp

(* Marshal and unmarshal the constants and metavariables pertaining to a single file.  We ignore the "current" data because that is only relevant during typechecking commands, whereas this comes at the end of typechecking a whole file.  We do NOT marshal the "holes" table because compiled files can't contain holes, and holedata potentially contains functional values. *)

let to_channel_origin chan origin flags =
  Constant.Table.to_channel_origin chan origin constants flags;
  Metatable.to_channel_origin chan origin metas flags

let link_definition f (Definition { mode; ty; tm; parametric }) =
  let ty = Link.term f ty in
  let tm =
    match tm with
    | `Axiom -> `Axiom
    | `Defined tm -> `Defined (Link.term f tm) in
  Definition { mode; ty; tm; parametric }

type origin_entry =
  (definition, Code.t) Result.t Constant.Table.origin_entry * unit Metatable.origin_entry

let find_file i = (Constant.Table.find_file i constants, Metatable.find_file i metas)

let add_file i (c, m) =
  invalidate ();
  Constant.Table.add_file i c constants;
  Metatable.add_file i m metas

(* Returns the new file data for constants and metas. *)
let from_istream_origin f chan i =
  invalidate ();
  (* NB in a tuple (a,b), OCaml executes b before a!  But we have to unmarshal the constants before the metas, because that's the order we marshaled them in, so we control the order of execution with let.  *)
  let cs = Constant.Table.from_istream_origin chan (Result.map (link_definition f)) i constants in
  let ms =
    Metatable.from_istream_origin chan
      {
        map =
          (fun _ df ->
            match df with
            | Ok df -> Ok (Link.metadef f df)
            | Error e -> Error e);
      }
      i metas in
  (cs, ms)

(* Add a new constant.  Only works on the current origin. *)
let add c d = consttable_add c (Ok d)

(* Set the definition of an already-defined constant.  Only works on the current origin. *)
let set : type mode.
    Constant.t ->
    mode Mode.t ->
    ?parametric:[ `Parametric | `Maybe_parametric | `Nonparametric ] ->
    (mode, mode emp, potential) term ->
    unit =
 fun c m ?parametric tm ->
  match Constant.Table.find_opt c constants with
  | Some (Ok (Definition { mode; ty; tm = _; parametric = p })) -> (
      match Mode.compare mode m with
      | Eq ->
          let tm = `Defined tm in
          let parametric = Option.value parametric ~default:p in
          consttable_add c (Ok (Definition { mode; tm; ty; parametric }))
      | Neq -> fatal (Anomaly "Global.set: mode mismatch"))
  | _ -> fatal (Anomaly "Global.set: constant not defined")

(* Add a new constant, but make it an error to access it. *)
let add_error c e = consttable_add c (Error e)

(* Add a new Global metavariable (e.g. local let-definition) to the new metas associated to the current command.  Its owner is the current one, and its local name, if any, should have been computed with Meta.local_name when it was created. *)
let add_meta ?local m ~termctx ~ty ~tm ~energy =
  let tm = (tm :> [ `Defined of ('mode, 'b, 's) term | `Axiom | `Undefined ]) in
  metatable_add m
    (Ok { tm; termctx; ty; energy; recursion = `Nonrecursive; owner = Meta.current_owner (); local })

let add_meta_error m e = metatable_add m (Error e)

(* Set the definition of a Global metavariable, required to already exist but not be defined.  The optional ?recursion argument records whether the definition contains occurrences of constants that were being defined when the metavariable was created (used when solving holes). *)
let set_meta m ?termctx ?recursion tm =
  match Metatable.find_opt m metas with
  | Some (Ok d) ->
      let d = Metadef.define ?recursion tm d in
      let d =
        match termctx with
        | Some termctx -> { d with termctx }
        | None -> d in
      metatable_add m (Ok d)
  | _ -> fatal (Anomaly "Global.set_meta: metavariable not defined")

(* Count all the unsolved holes, from all origins. *)
let unsolved_holes () =
  Metatable.fold
    {
      fold =
        (fun _ v count ->
          match v with
          | Ok { tm = `Undefined; _ } -> count + 1
          | _ -> count);
    }
    metas 0

(* Count only the unsolved holes from the current origin. *)
let current_unsolved_holes () =
  Metatable.fold_current
    {
      fold =
        (fun _ v count ->
          match v with
          | Ok { tm = `Undefined; _ } -> count + 1
          | _ -> count);
    }
    metas 0

(* Notify the user about how many unsolved holes there are. *)
let notify_holes () =
  let n = unsolved_holes () in
  if n > 0 then Reporter.emit (Open_holes n)

(* Since holes are not allowed inside all commands, we need to keep track of whether we're in a command that allows holes and check for it.  We use a global mutable state for this.  We also record all the holes *created* by the current command in a separate list so they can be reported to the user, and what is known so far about whether the currently executing command must be parametric.. *)

type hole = { meta : Meta.wrapped; printable : printable; startpos : int; endpos : int }

(* The unification metavariables created by a command are stored only in the state of that command, since they are either solved by the time it succeeds or else cause it to fail.  For each one we store its type and context, which are needed only while it is unsolved, and its solution if it has been solved during the command.  Since the state of the command is a Speculable, all of these are discarded if a speculative computation that creates or solves them backtracks.  When the command succeeds, the solutions are written into the cells shared by their occurrences (see Term.meta_kind), so that the table is no longer needed.

   We also record the depth of speculation (see Origin.speculate) at which each one was created.  A speculation can only solve the unification metavariables created inside it, not those from outside it, since if it backtracks, values created outside it that saw the solution (e.g. by forcing lazy computations that depended on it) would remain incorrect.  When a speculation succeeds, the unification metavariables created inside it now belong to the enclosing computation, so we decrease their recorded depth to match.

   The context is computed lazily, since it is needed only if the metavariable is compared to itself, read back with a nontrivial environment, or displayed.  It must not be read back for display, so its thunk sets the display flag explicitly (see Check.make_unif).  The table is never marshaled, so it can contain such functional values. *)
module Unifdata = struct
  type ('mode, 'a, 'b, 's) t = {
    meta : ('mode, 'a, 'b, kinetic) Meta.t;
    unif : ('mode, 'b, kinetic) term option ref;
    ctx : ('mode, 'a, 'b) Ctx.t;
    ty : ('mode, 'b, kinetic) term;
    termctx : ('mode, 'a, 'b) termctx Lazy.t;
    solution : ('mode, 'b, kinetic) term option;
    depth : int;
    (* Where the metavariable came from, and the error to report there if it isn't solved. *)
    loc : Asai.Range.t option;
    err : Reporter.Code.t;
    (* A delayed metavariable stands for a term that can't be used yet, because its correctness depends on a postponed constraint.  It can't be solved by unification, only released by that constraint once it is satisfied (see Postponed).  Since it evaluates to a neutral blocked on it, like any other unsolved unification metavariable, computations involving it are redone once it is released. *)
    delayed : bool;
  }
end

module Uniftable = Meta.Table.Make_map (Unifdata)

(* A postponed constraint is a problem, such as an equality or subtyping check, that couldn't be decided because it was stuck on unsolved unification metavariables, its blockers.  We retry it only once one of its blockers has been solved (or, at the end of a command, once anything has been solved since we last tried it, since the blockers are not necessarily complete), and only at "safe points" where this can't happen re-entrantly inside another comparison.  Like a unification metavariable, it can only be retried at the depth of speculation where it was created (see Unifdata).

   Its attempt is a closure that does whatever is appropriate if the problem is decided, such as releasing a delayed metavariable or reporting an error, and otherwise returns new blockers.  If it is never decided, its report is called at the end of the command to report it. *)
module Postponed = struct
  type t = {
    id : int;
    blockers : Value.blocker list;
    (* The number of metavariable solutions in the current command when we last attempted this constraint. *)
    seen : int;
    depth : int;
    attempt : unit -> [ `Done | `Stuck of Value.blocker list ];
    report : unit -> unit;
  }
end

type current_command = {
  holes_allowed : (unit, string) Result.t;
  current_holes : hole Bwd.t;
  unifs : Uniftable.t;
  postponed : Postponed.t list;
  (* The number of unification metavariables that have been solved or released during this command, so that we can tell whether anything has been solved since a postponed constraint was last attempted. *)
  solves : int;
  parametric : [ `Must_be_parametric | `Maybe_parametric | `Nonparametric ];
}

let empty_command holes_allowed origin parametric =
  {
    holes_allowed;
    current_holes = Emp;
    unifs = Uniftable.empty origin;
    postponed = [];
    solves = 0;
    parametric;
  }

let current_command : current_command Speculable.t =
  Speculable.make (empty_command (Error "run") Top `Maybe_parametric)

(* Set and get parametric-ness *)

let set_nonparametric name =
  if (Speculable.get current_command).parametric = `Must_be_parametric then
    match name with
    | Some name -> fatal (Axiom_in_parametric_definition (PConstant name))
    | None -> fatal (Anomaly "set_nonparametric found must_be without constant")
  else Speculable.modify current_command (fun d -> { d with parametric = `Nonparametric })

let set_parametric name =
  if (Speculable.get current_command).parametric = `Nonparametric then
    fatal (Locked_constant (PConstant name))
  else Speculable.modify current_command (fun d -> { d with parametric = `Must_be_parametric })

let set_maybe_parametric () =
  Speculable.modify current_command (fun d -> { d with parametric = `Maybe_parametric })

let get_parametric () =
  match (Speculable.get current_command).parametric with
  | `Nonparametric -> `Nonparametric
  | `Must_be_parametric | `Maybe_parametric -> `Parametric

(* Add a new unification metavariable, with its cell, to the table of the current command. *)
let add_unif : type mode a b.
    (mode, a, b, kinetic) Meta.t ->
    (mode, b, kinetic) term option ref ->
    ctx:(mode, a, b) Ctx.t ->
    ty:(mode, b, kinetic) term ->
    termctx:(mode, a, b) termctx Lazy.t ->
    loc:Asai.Range.t option ->
    err:Reporter.Code.t ->
    delayed:bool ->
    unit =
 fun meta unif ~ctx ~ty ~termctx ~loc ~err ~delayed ->
  Speculable.modify current_command (fun d ->
      {
        d with
        unifs =
          Uniftable.add meta
            {
              meta;
              unif;
              ctx;
              ty;
              termctx;
              solution = None;
              depth = Origin.speculation_depth ();
              loc;
              err;
              delayed;
            }
            d.unifs;
      })

(* Look up the data of a unification metavariable.  This is only possible during the command that created it. *)
let find_unif : type mode a b. (mode, a, b, kinetic) Meta.t -> (mode, a, b, kinetic) Unifdata.t =
 fun meta ->
  match Uniftable.find_opt meta (Speculable.get current_command).unifs with
  | Some d -> d
  | None ->
      fatal
        (Anomaly
           ("unification metavariable used outside the command that created it: " ^ Meta.name meta))

(* The context in which a unification metavariable was created. *)
let unif_ctx : type mode a b. (mode, a, b, kinetic) Meta.t -> (mode, a, b) Ctx.t =
 fun meta -> (find_unif meta).ctx

(* The location of a unification metavariable, and the error to report there if it isn't solved. *)
let unif_error : type mode a b.
    (mode, a, b, kinetic) Meta.t -> Asai.Range.t option * Reporter.Code.t =
 fun meta ->
  let d = find_unif meta in
  (d.loc, d.err)

(* Whether something created at a given depth of speculation belongs to the current one, i.e. was created inside the innermost current speculation (or a speculation that has since succeeded into it). *)
let at_current_depth name depth =
  let current = Origin.speculation_depth () in
  if depth > current then fatal (Anomaly (name ^ " deeper than current speculation"))
  else depth = current

(* Whether a unification metavariable can be solved by unification: it must not be delayed, and it must have been created at the current depth of speculation. *)
let unif_assignable : type mode a b. (mode, a, b, kinetic) Meta.t -> bool =
 fun meta ->
  let d = find_unif meta in
  (not d.delayed) && at_current_depth ("unification metavariable " ^ Meta.name meta) d.depth

(* When a speculation succeeds, the unification metavariables and postponed constraints created inside it now belong to the enclosing computation. *)
let () =
  Origin.on_speculation_success @@ fun () ->
  let depth = Origin.speculation_depth () in
  Speculable.modify current_command (fun c ->
      {
        c with
        unifs = Uniftable.map { map = (fun d -> { d with depth = min d.depth depth }) } c.unifs;
        postponed = List.map (fun p -> Postponed.{ p with depth = min p.depth depth }) c.postponed;
      })

let set_unif_solution : type mode a b.
    string -> (mode, a, b, kinetic) Meta.t -> (mode, b, kinetic) term -> unit =
 fun what meta tm ->
  let d = find_unif meta in
  match d.solution with
  | Some _ -> fatal (Anomaly (what ^ " already-solved unification metavariable " ^ Meta.name meta))
  | None ->
      invalidate ();
      Speculable.modify current_command (fun c ->
          {
            c with
            unifs = Uniftable.add meta { d with solution = Some tm } c.unifs;
            solves = c.solves + 1;
          })

(* Record the solution of an unsolved unification metavariable in the table of the current command.  If this happens during a speculative computation that later backtracks, the solution is discarded with the rest of the table.  It is written into the cell of the metavariable only when the command succeeds (see finish_unifs). *)
let solve_unif : type mode a b. (mode, a, b, kinetic) Meta.t -> (mode, b, kinetic) term -> unit =
 fun meta tm ->
  if not (unif_assignable meta) then
    fatal (Anomaly ("solving delayed or outer unification metavariable " ^ Meta.name meta))
  else set_unif_solution "solving" meta tm

(* Release a delayed metavariable, giving it its value, once the constraint it was waiting for has been decided.  If that constraint failed, its value is a failed term. *)
let release_unif : type mode a b. (mode, a, b, kinetic) Meta.t -> (mode, b, kinetic) term -> unit =
 fun meta tm ->
  let d = find_unif meta in
  if not (d.delayed && at_current_depth ("delayed metavariable " ^ Meta.name meta) d.depth) then
    fatal (Anomaly ("releasing non-delayed or outer metavariable " ^ Meta.name meta))
  else set_unif_solution "releasing" meta tm

(* The solution of a unification metavariable, if it has one: either written into its cell when its command succeeded, or else in the table of the current command. *)
let unif_solution : type mode a b.
    (mode, a, b, kinetic) Meta.t ->
    (mode, b, kinetic) term option ref ->
    (mode, b, kinetic) term option =
 fun meta unif ->
  match !unif with
  | Some _ as solution -> solution
  | None -> (find_unif meta).solution

(* The solution of a unification metavariable for display: like unif_solution, but if its table is gone (because its command has ended without solving it), we just say it has no solution. *)
let unif_solution_opt : type mode a b.
    (mode, a, b, kinetic) Meta.t ->
    (mode, b, kinetic) term option ref ->
    (mode, b, kinetic) term option =
 fun meta unif ->
  match !unif with
  | Some _ as solution -> solution
  | None ->
      Option.bind (Uniftable.find_opt meta (Speculable.get current_command).unifs) (fun d ->
          d.solution)

(* Whether a unification metavariable has been solved, and if so whether its solution has been written into its cell (and hence is permanent) or is only in the table of the current command (and hence could still be backtracked). *)
let unif_status : type mode a b.
    (mode, a, b, kinetic) Meta.t ->
    (mode, b, kinetic) term option ref ->
    [ `Unsolved | `Speculative | `Written ] =
 fun meta unif ->
  match !unif with
  | Some _ -> `Written
  | None -> (
      match (find_unif meta).solution with
      | Some _ -> `Speculative
      | None -> `Unsolved)

(* The stored context and type of a metavariable of either kind. *)
let meta_termctx : type mode a b s e.
    (mode, a, b, s) Meta.t -> (mode, b, s, e) meta_kind -> (mode, a, b) termctx =
 fun meta -> function
  | Global_meta -> (find_meta meta).termctx
  | Unif_meta _ -> Lazy.force (find_unif meta).termctx

let meta_ty : type mode a b s e.
    (mode, a, b, s) Meta.t -> (mode, b, s, e) meta_kind -> (mode, b, kinetic) term =
 fun meta -> function
  | Global_meta -> (find_meta meta).ty
  | Unif_meta _ -> (find_unif meta).ty

(* At the end of a command, all its unification metavariables must be solved, or else it fails, and we write their solutions into them.  If the command has already failed for some other reason, we don't report its unsolved unification metavariables, since they are likely to be consequences of that failure. *)
(* Iterate over the currently unsolved unification metavariables. *)
type unsolved_unif_iter = {
  it :
    'mode 'a 'b.
    ('mode, 'a, 'b, kinetic) Meta.t -> ('mode, 'a, 'b) Ctx.t -> ('mode, 'b, kinetic) term -> unit;
}

let iter_unsolved_unifs f =
  Uniftable.fold
    {
      fold =
        (fun { meta; ctx; ty; solution; _ } () -> if Option.is_none solution then f.it meta ctx ty);
    }
    (Speculable.get current_command).unifs ()

(* Some unification metavariables can be solved at the end of a command even if nothing has constrained them, because their type has only one element up to eta-conversion.  That's defined in Unify, downstream of here. *)
let singleton_unif_solver : (unit -> unit) ref = ref (fun () -> ())
let set_singleton_unif_solver f = singleton_unif_solver := f
let solve_singleton_unifs () = !singleton_unif_solver ()

let count_unsolved_unifs () =
  Uniftable.fold
    { fold = (fun { solution; _ } n -> if Option.is_none solution then n + 1 else n) }
    (Speculable.get current_command).unifs 0

(* Report the error of each unsolved unification metavariable.  Metavariables can be created together for the same term, such as the boundary of a primary argument, the fields of an expansion, or the type of a placeholder, and these have the same location.  Since at most one error is useful for each term, we report only the first. *)
let report_unsolved_unifs () =
  let seen = ref [] in
  Uniftable.fold
    {
      fold =
        (fun { solution; loc; err; delayed; _ } () ->
          (* A delayed metavariable is unsolved only if its constraint is, and that is reported instead. *)
          if Option.is_none solution && (not delayed) && not (List.mem loc !seen) then (
            seen := loc :: !seen;
            mortal ?loc err));
    }
    (Speculable.get current_command).unifs ()

(* Postpone a constraint, to be retried later. *)
let postpone_counter = ref 0

let postpone ~blockers ~attempt ~report =
  incr postpone_counter;
  Speculable.modify current_command (fun c ->
      {
        c with
        postponed =
          c.postponed
          @ [
              {
                id = !postpone_counter;
                blockers;
                seen = c.solves;
                depth = Origin.speculation_depth ();
                attempt;
                report;
              };
            ];
      })

(* Whether a postponed constraint should be retried, because one of its blockers has been solved, or if [stale], because anything has been solved since it was last attempted. *)
let woken ~stale (p : Postponed.t) =
  if stale then p.seen < (Speculable.get current_command).solves
  else
    List.exists (fun (Value.Blocker (meta, unif)) -> unif_status meta unif <> `Unsolved) p.blockers

(* Retry the postponed constraints that have been woken, at the current depth of speculation, until none remain.  Return whether anything happened, i.e. a constraint was decided or a metavariable was solved.  Attempting a constraint may lead back here, e.g. by typechecking a term, but we don't retry re-entrantly. *)
let retrying = ref false

let retry_postponed ?(stale = false) () =
  if !retrying then false
  else (
    retrying := true;
    Fun.protect ~finally:(fun () -> retrying := false) @@ fun () ->
    let start = (Speculable.get current_command).solves in
    let decided = ref false in
    let rec loop () =
      let c = Speculable.get current_command in
      match
        List.find_opt
          (fun (p : Postponed.t) ->
            at_current_depth "postponed constraint" p.depth && woken ~stale p)
          c.postponed
      with
      | None -> ()
      | Some p ->
          (* We remove the constraint while attempting it, so that it doesn't get retried inside itself. *)
          Speculable.modify current_command (fun c ->
              { c with postponed = List.filter (fun (q : Postponed.t) -> q.id <> p.id) c.postponed });
          (* If the attempt fails with a fatal error, such as a dependent one from comparing a failed term, we report it and regard the constraint as decided, so that the rest of the command can finish. *)
          (match Reporter.mortalize ~fallback:(fun () -> `Done) p.attempt with
          | `Done -> decided := true
          | `Stuck blockers ->
              Speculable.modify current_command (fun c ->
                  { c with postponed = c.postponed @ [ { p with blockers; seen = c.solves } ] }));
          loop () in
    loop ();
    !decided || (Speculable.get current_command).solves > start)

(* Solve everything we can at the end of a command, or before it displays something: retry the postponed constraints, and solve the unification metavariables whose types are singletons, until nothing changes. *)
let rec settle_unifs () =
  let retried = retry_postponed () in
  let retried_stale = retry_postponed ~stale:true () in
  let before = (Speculable.get current_command).solves in
  solve_singleton_unifs ();
  if retried || retried_stale || (Speculable.get current_command).solves > before then
    settle_unifs ()

(* Report the undecided postponed constraints.  A constraint that is stuck only on delayed metavariables is stuck because of their constraints, which are reported instead. *)
let report_postponed () =
  List.iter
    (fun (p : Postponed.t) ->
      if not (List.for_all (fun (Value.Blocker (meta, _)) -> (find_unif meta).delayed) p.blockers)
      then p.report ())
    (Speculable.get current_command).postponed

let finish_unifs () =
  if not (moribund ()) then settle_unifs ();
  (* An undecided constraint and the unsolved metavariables it is stuck on are both worth reporting, since the constraint may be undecided only because of them. *)
  if not (moribund ()) then (
    report_postponed ();
    report_unsolved_unifs ());
  (* Even if the command failed, the constants it was defining may still be used by later commands, with their failed parts failing silently if they are inspected.  Thus, an unsolved unification metavariable, whose table is about to go away, must become such a failed part. *)
  Uniftable.fold
    {
      fold =
        (fun { unif; solution; _ } () ->
          unif := Some (Option.value solution ~default:(Term.Failed Kinetic)));
    }
    (Speculable.get current_command).unifs ()

(* Whether the current command has created any unification metavariables that are not yet solved, and hence will fail at its end unless they are.  A command that produces output before then, such as echo, can check this to avoid producing it. *)
let unsolved_unifs () = count_unsolved_unifs () > 0

(* At successful completion of a command, notify the user of generated holes.  Use make_msg to show the number of holes, and also emit the holes separately to be shown in the goals buffer.  This is a subroutine of run_command and friends, below. *)
let end_command (offset, make_msg) =
  finish_unifs ();
  (* If the command ended up being parametric, we must retroactively label all the holes as parametric, so that they can only be filled using parametric constants, and oppositely. *)
  let update_parametric : type mode a b s.
      (mode, a, b, s) Metadef.hole -> (mode, a, b, s) Metadef.hole =
   fun h ->
    let parametric =
      match (Speculable.get current_command).parametric with
      | `Must_be_parametric -> `Parametric
      | `Maybe_parametric when not (Dim.Endpoints.internal ()) -> `Parametric
      | _ -> `Nonparametric in
    { h with parametric } in
  (* If the command had any errors, it will fail, so its holes won't exist; thus we don't display either the message about the command or the hole goals. *)
  let failed = moribund () in
  if not failed then
    Option.iter emit (make_msg (Bwd.length (Speculable.get current_command).current_holes));
  Mbwd.miter
    (fun [ ({ meta = Meta.Wrap m; printable; _ } : hole) ] ->
      (* We intentionally do not "locate" this emission, since we want to display only the hole context and type, not its location in the source. *)
      if not failed then emit (Hole (Meta.name m, printable));
      match Holetable.find_opt m holes with
      | Some h -> Holetable.add m (update_parametric h) holes
      | None -> ())
    [ (Speculable.get current_command).current_holes ];
  (* Current_command.modify (fun d -> { d with current_holes = Emp; parametric = `Maybe_parametric }) *)
  ( offset,
    Bwd_extra.to_list_map
      (fun ({ meta = Wrap meta; startpos; endpos; _ } : hole) ->
        (Meta.hole_number meta, startpos, endpos))
      (Speculable.get current_command).current_holes )

(* Run a command.  If it reports any errors, even if it returns, it fails with a silent fatal error.  This has to happen inside the Origin command functions, so that in interactive mode they undo its effects, such as definitions with failed parts or partially failed hole solutions. *)
let in_command init f =
  Reporter.failing_on_errors ~why:"command" @@ fun () ->
  (* A command can run other commands, as when an import loads a file, so afterwards we restore the state of the command that was running before. *)
  let old = Speculable.get current_command in
  Speculable.set current_command init;
  Fun.protect ~finally:(fun () -> Speculable.set current_command old) @@ fun () ->
  end_command (f ())

(* The different versions correspond to the Origin command functions that they call. *)

let run_command ~holes_allowed f =
  Origin.do_command @@ fun () ->
  in_command (empty_command holes_allowed (Origin.current ()) `Maybe_parametric) f

let run_command_then_undo ~holes_allowed f =
  Origin.do_command_then_undo @@ fun () ->
  in_command (empty_command holes_allowed (Origin.current ()) `Maybe_parametric) f

(* In the rewind cases, we have to restore the parametric-ness information from the past also. *)
let rewind_command ~parametric ~holes_allowed instant f =
  let parametric =
    match parametric with
    | `Parametric -> `Must_be_parametric
    | `Nonparametric -> `Nonparametric in
  Origin.rewind_command instant @@ fun () ->
  in_command (empty_command holes_allowed (Origin.current ()) parametric) f

let rewind_command_then_undo ~parametric ~holes_allowed instant f =
  let parametric =
    match parametric with
    | `Parametric -> `Must_be_parametric
    | `Nonparametric -> `Nonparametric in
  Origin.rewind_command_then_undo instant @@ fun () ->
  in_command (empty_command holes_allowed (Origin.current ()) parametric) f

(* For white box testing *)
let run f =
  Speculable.set current_command (empty_command (Error "run") Top `Maybe_parametric);
  f ()

(* Add a new hole. *)
let add_hole m loc ~vars ~termctx ~ty ~status ~li ~ri =
  match (Origin.holes_allowed (), (Speculable.get current_command).holes_allowed) with
  | Error where, _ ->
      fatal
        (No_holes_allowed (where :> [ `Command of string | `File of string | `Other of string ]))
  | _, Error msg -> fatal (No_holes_allowed (`Command msg))
  | Ok (), Ok () ->
      metatable_add m
        (Ok
           {
             tm = `Undefined;
             termctx;
             ty;
             energy = Status.energy status;
             recursion = `Nonrecursive;
             owner = Meta.current_owner ();
             local = None;
           });
      Holetable.add m
        {
          status;
          vars;
          li;
          ri;
          parametric = get_parametric ();
          beingdefined = Positivity.beingdefined ();
        }
        holes;
      let s, e = Asai.Range.split loc in
      Speculable.set current_command
        {
          (Speculable.get current_command) with
          current_holes =
            Snoc
              ( (Speculable.get current_command).current_holes,
                {
                  meta = Wrap m;
                  printable = PHole (Origin.current (), vars, termctx, ty);
                  startpos = s.offset;
                  endpos = e.offset;
                } );
        }

(* Temporarily set the value of a constant to execute a callback, and restore it afterwards. *)
let with_definition : type mode a.
    Constant.t ->
    mode Mode.t ->
    [ `Axiom | `Defined of (mode, mode emp, potential) term ] ->
    (unit -> a) ->
    a =
 fun c m tm f ->
  match Constant.Table.find_opt c constants with
  | Some (Ok (Definition { mode; ty; _ }) as old) -> (
      let parametric =
        match (Speculable.get current_command).parametric with
        | `Nonparametric -> `Nonparametric
        | `Must_be_parametric | `Maybe_parametric -> `Maybe_parametric in
      match Mode.compare mode m with
      | Eq ->
          consttable_add c (Ok (Definition { mode; ty; tm; parametric }));
          Fun.protect ~finally:(fun () -> consttable_add c old) f
      | Neq -> fatal (Anomaly "Global.set: mode mismatch"))
  | Some (Error _ as old) ->
      (* If the constant is currently unusable, we just retain that state. *)
      Fun.protect ~finally:(fun () -> consttable_add c old) f
  | _ -> fatal (Anomaly "missing definition in with_definition")

(* Similarly, temporarily set the value of a global metavariable, which could be either permanent or current. *)
let with_meta_definition m tm f =
  match Metatable.find_opt m metas with
  | Some (Ok olddf as old) ->
      metatable_add m (Ok (Metadef.define tm olddf));
      Fun.protect ~finally:(fun () -> metatable_add m old) f
  | Some (Error _ as old) ->
      (* If the metavariable is currently unusable, we just retain that state. *)
      Fun.protect ~finally:(fun () -> metatable_add m old) f
  | None ->
      (* If the metavariable isn't found, that means that when we created it we didn't have a type for it.  That, in turn, means that the user doesn't have a name for it, since the metavariable is only bound to a user name in a "let rec".  So we don't need to do anything. *)
      f ()
