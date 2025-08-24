(* This module should not be opened, but used qualified. *)

open Bwd
open Util
open Tbwd
open Reporter
open Term
open Printable
open Origin

(* The global environment of constants and definition-local metavariables. *)

(* Each global constant either is an axiom or has a definition (a case tree).  The latter includes canonical types.  *)
type definition =
  [ `Axiom | `Defined of (emp, potential) term ]
  (* A parametric constant can have external degeneracies applied to it, while a nonparametric one can't.  A maybe-parametric one is one currently being typechecked which hasn't yet been concluded to be nonparametric. *)
  * [ `Parametric | `Nonparametric | `Maybe_parametric ]

(* The versioned global table of defined constants. *)
let constants : ((emp, kinetic) term * definition, Code.t) Result.t Constant.Table.t =
  Constant.Table.make ()

(* Global metavariables have only a definition (or an error indicating that they can't be correctly accessed, such as if typechecking failed earlier). *)
module Metatable = Meta.Table.Make (struct
  type ('x, 'a, 'b, 's) t = (('a, 'b, 's) Metadef.t, Code.t) Result.t
end)

module Holetable = Meta.Table.Make (struct
  type ('x, 'a, 'b, 's) t = ('a, 'b, 's) Metadef.hole
end)

(* The versioned global tables for metavariables (including holes) and for special hole data. *)
let metas : unit Metatable.t = Metatable.make ()
let holes : unit Holetable.t = Holetable.make ()

(* Look up a constant. *)
let find c =
  match Constant.Table.find_opt c constants with
  | Some (Ok (ty, tm)) -> (ty, tm)
  | Some (Error e) -> fatal e
  | None -> fatal (Undefined_constant (PConstant c))

(* Similarly, look up a metavariable. *)
let find_meta m =
  match Metatable.find_opt m metas with
  | Some (Ok d) -> d
  | Some (Error e) -> fatal e
  | None -> fatal (Anomaly ("undefined metavariable: " ^ Meta.name m))

(* Combine all the data for a hole, to return them when looked up. *)
type find_hole =
  | Found_hole : {
      meta : ('a, 'b, 's) Meta.t;
      instant : Instant.t;
      termctx : ('a, 'b) termctx;
      ty : ('b, kinetic) term;
      status : ('b, 's) Status.status;
      vars : (string option, 'a) Bwv.t;
      li : No.interval;
      ri : No.interval;
      parametric : [ `Parametric | `Nonparametric ];
    }
      -> find_hole

(* Subroutine for returning those data. *)
let return_hole : type a b s.
    (a, b, s) Meta.t ->
    ((a, b, s) Metadef.t, Code.t) Result.t ->
    (a, b, s) Metadef.hole option ->
    find_hole option =
 fun meta def hole ->
  match (def, hole) with
  | Ok { tm = `Undefined; termctx; ty; _ }, Some { status; vars; li; ri; parametric } -> (
      match Meta.origin meta with
      | Instant instant ->
          Some (Found_hole { meta; instant; termctx; ty; status; vars; li; ri; parametric })
      | _ -> fatal (Anomaly "timeless hole"))
  | Error e, _ -> fatal e
  | _ -> None

let find_hole i =
  let open Monad.Ops (Monad.Maybe) in
  match
    let* (Entry (meta, def)) = Metatable.find_hole_opt i metas in
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
          | Some h -> Snoc (hs, h)
          | None -> hs);
    }
    metas Emp

(* Marshal and unmarshal the constants and metavariables pertaining to a single file.  We ignore the "current" data because that is only relevant during typechecking commands, whereas this comes at the end of typechecking a whole file.  We do NOT marshal the "holes" table because compiled files can't contain holes, and holedata potentially contains functional values. *)

let to_channel_origin chan origin flags =
  Constant.Table.to_channel_origin chan origin constants flags;
  Metatable.to_channel_origin chan origin metas flags

let link_definition f df =
  match df with
  | `Axiom, p -> (`Axiom, p)
  | `Defined tm, p -> (`Defined (Link.term f tm), p)

type origin_entry =
  ((emp, kinetic) term * definition, Code.t) Result.t Constant.Table.origin_entry
  * unit Metatable.origin_entry

let find_file i = (Constant.Table.find_file i constants, Metatable.find_file i metas)

let add_file i (c, m) =
  Constant.Table.add_file i c constants;
  Metatable.add_file i m metas

(* Returns the new file data for constants and metas. *)
let from_channel_origin f chan i =
  (* NB in a tuple (a,b), OCaml executes b before a!  But we have to unmarshal the constants before the metas, because that's the order we marshaled them in, so we control the order of execution with let.  *)
  let cs =
    Constant.Table.from_channel_origin chan
      (Result.map (fun (tm, df) -> (Link.term f tm, link_definition f df)))
      i constants in
  let ms =
    Metatable.from_channel_origin chan
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
let add c ty df = Constant.Table.add c (Ok (ty, df)) constants

(* Set the definition of an already-defined constant.  Only works on the current origin. *)
let set c df =
  match Constant.Table.find_opt c constants with
  | Some (Ok (ty, _)) -> Constant.Table.add c (Ok (ty, df)) constants
  | _ -> fatal (Anomaly "Global.set: constant not defined")

(* Add a new constant, but make it an error to access it. *)
let add_error c e = Constant.Table.add c (Error e) constants

(* Add a new Global metavariable (e.g. local let-definition) to the new metas associated to the current command. *)
let add_meta m ~termctx ~ty ~tm ~energy =
  let tm = (tm :> [ `Defined of ('b, 's) term | `Axiom | `Undefined ]) in
  Metatable.add m (Ok { tm; termctx; ty; energy }) metas

(* Set the definition of a Global metavariable, required to already exist but not be defined. *)
let set_meta m ~tm =
  match Metatable.find_opt m metas with
  | Some (Ok d) -> Metatable.add m (Ok { d with tm = `Defined tm }) metas
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

(* Since holes are not allowed inside all commands, we need to keep track of whether we're in a command that allows holes and check for it.  We use a state effect for this.  We also record all the holes *created* by the current command in a separate list so they can be reported to the user, and what is known so far about whether the currently executing command must be parametric.. *)

module Command_state = struct
  type hole = { meta : Meta.wrapped; printable : printable; startpos : int; endpos : int }

  type t = {
    holes_allowed : (unit, string) Result.t;
    current_holes : hole Bwd.t;
    parametric : [ `Must_be_parametric | `Maybe_parametric | `Nonparametric ];
  }
end

module Current_command = State.Make (Command_state)

let () =
  Current_command.register_printer (function
    | `Get -> Some "unhandled Current_command.get effect"
    | `Set _ -> Some "unhandled Current_command.set effect")

(* Set and get parametric-ness *)

let set_nonparametric name =
  Current_command.modify (fun d ->
      if d.parametric = `Must_be_parametric then
        match name with
        | Some name -> fatal (Axiom_in_parametric_definition (PConstant name))
        | None -> fatal (Anomaly "set_nonparametric found must_be without constant")
      else { d with parametric = `Nonparametric })

let set_parametric name =
  Current_command.modify (fun d ->
      if d.parametric = `Nonparametric then fatal (Locked_constant (PConstant name))
      else { d with parametric = `Must_be_parametric })

let set_maybe_parametric () =
  Current_command.modify (fun d -> { d with parametric = `Maybe_parametric })

let get_parametric () =
  match (Current_command.get ()).parametric with
  | `Nonparametric -> `Nonparametric
  | `Must_be_parametric | `Maybe_parametric -> `Parametric

(* At successful completion of a command, notify the user of generated holes.  Use make_msg to show the number of holes, and also emit the holes separately to be shown in the goals buffer.  This is a subroutine of run_command and friends, below. *)
let end_command (offset, make_msg) =
  let d = Current_command.get () in
  (* If the command ended up being parametric, we must retroactively label all the holes as parametric, so that they can only be filled using parametric constants, and oppositely. *)
  let update_parametric : type a b s. (a, b, s) Metadef.hole -> (a, b, s) Metadef.hole =
   fun h ->
    let parametric =
      match d.parametric with
      | `Must_be_parametric -> `Parametric
      | `Maybe_parametric when not (Dim.Endpoints.internal ()) -> `Parametric
      | _ -> `Nonparametric in
    { h with parametric } in
  Option.iter emit (make_msg (Bwd.length d.current_holes));
  Mbwd.miter
    (fun [ ({ meta = Meta.Wrap m; printable; _ } : Command_state.hole) ] ->
      (* We intentionally do not "locate" this emission, since we want to display only the hole context and type, not its location in the source. *)
      emit (Hole (Meta.name m, printable));
      Holetable.update m (Option.map update_parametric) holes)
    [ d.current_holes ];
  (* Current_command.modify (fun d -> { d with current_holes = Emp; parametric = `Maybe_parametric }) *)
  ( offset,
    Bwd_extra.to_list_map
      (fun ({ meta = Wrap meta; startpos; endpos; _ } : Command_state.hole) ->
        (Meta.hole_number meta, startpos, endpos))
      d.current_holes )

(* Run a command.  The different versions correspond to the Origin command functions that they call. *)

let run_command ~holes_allowed f =
  Origin.do_command @@ fun () ->
  Current_command.run ~init:{ holes_allowed; current_holes = Emp; parametric = `Maybe_parametric }
  @@ fun () -> end_command (f ())

let run_command_then_undo ~holes_allowed f =
  Origin.do_command_then_undo @@ fun () ->
  Current_command.run ~init:{ holes_allowed; current_holes = Emp; parametric = `Maybe_parametric }
  @@ fun () -> end_command (f ())

(* In the rewind cases, we have to restore the parametric-ness information from the past also. *)
let rewind_command ~parametric ~holes_allowed instant f =
  let parametric =
    match parametric with
    | `Parametric -> `Must_be_parametric
    | `Nonparametric -> `Nonparametric in
  Origin.rewind_command instant @@ fun () ->
  Current_command.run ~init:{ holes_allowed; current_holes = Emp; parametric } @@ fun () ->
  end_command (f ())

let rewind_command_then_undo ~parametric ~holes_allowed instant f =
  let parametric =
    match parametric with
    | `Parametric -> `Must_be_parametric
    | `Nonparametric -> `Nonparametric in
  Origin.rewind_command_then_undo instant @@ fun () ->
  Current_command.run ~init:{ holes_allowed; current_holes = Emp; parametric } @@ fun () ->
  end_command (f ())

(* For white box testing *)
let run f =
  Current_command.run
    ~init:{ holes_allowed = Error "run"; current_holes = Emp; parametric = `Maybe_parametric }
    f

(* Add a new hole. *)
let add_hole m loc ~vars ~termctx ~ty ~status ~li ~ri =
  let cmd = Current_command.get () in
  match (Origin.holes_allowed (), cmd.holes_allowed) with
  | Error where, _ ->
      fatal
        (No_holes_allowed (where :> [ `Command of string | `File of string | `Other of string ]))
  | _, Error msg -> fatal (No_holes_allowed (`Command msg))
  | Ok (), Ok () ->
      Metatable.add m (Ok { tm = `Undefined; termctx; ty; energy = Status.energy status }) metas;
      Holetable.add m { status; vars; li; ri; parametric = get_parametric () } holes;
      let s, e = Asai.Range.split loc in
      Current_command.set
        {
          cmd with
          current_holes =
            Snoc
              ( cmd.current_holes,
                {
                  meta = Wrap m;
                  printable = PHole (Origin.current (), vars, termctx, ty);
                  startpos = s.offset;
                  endpos = e.offset;
                } );
        }

(* Temporarily set the value of a constant to execute a callback, and restore it afterwards. *)
let with_definition c df f =
  match Constant.Table.find_opt c constants with
  | Some (Ok (ty, _) as old) ->
      let d = Current_command.get () in
      let p =
        match d.parametric with
        | `Nonparametric -> `Nonparametric
        | `Must_be_parametric | `Maybe_parametric -> `Maybe_parametric in
      Constant.Table.add c (Ok (ty, (df, p))) constants;
      Fun.protect ~finally:(fun () -> Constant.Table.add c old constants) f
  | Some (Error _ as old) ->
      (* If the constant is currently unusable, we just retain that state. *)
      Fun.protect ~finally:(fun () -> Constant.Table.add c old constants) f
  | _ -> fatal (Anomaly "missing definition in with_definition")

(* Similarly, temporarily set the value of a global metavariable, which could be either permanent or current. *)
let with_meta_definition m tm f =
  match Metatable.find_opt m metas with
  | Some (Ok olddf as old) ->
      Metatable.add m (Ok (Metadef.define tm olddf)) metas;
      Fun.protect ~finally:(fun () -> Metatable.add m old metas) f
  | Some (Error _ as old) ->
      (* If the metavariable is currently unusable, we just retain that state. *)
      Fun.protect ~finally:(fun () -> Metatable.add m old metas) f
  | _ ->
      (* If the metavariable isn't found, that means that when we created it we didn't have a type for it.  That, in turn, means that the user doesn't have a name for it, since the metavariable is only bound to a user name in a "let rec".  So we don't need to do anything. *)
      f ()

(* Temporarily set the value of a constant to produce an error, and restore it afterwards. *)
let without_definition c err f =
  match Constant.Table.find_opt c constants with
  | Some old ->
      Constant.Table.add c (Error err) constants;
      Fun.protect ~finally:(fun () -> Constant.Table.add c old constants) f
  | _ -> fatal (Anomaly "missing definition in without_definition")

(* Similarly, temporarily set the value of a global metavariable to produce an error. *)
let without_meta_definition m err f =
  match Metatable.find_opt m metas with
  | Some old ->
      Metatable.add m (Error err) metas;
      Fun.protect ~finally:(fun () -> Metatable.add m old metas) f
  | _ -> f ()
