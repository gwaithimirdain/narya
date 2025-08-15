(* The "origin" of a constant or metavariable is either the toplevel (for built-ins), a file (including command-line exec strings and stdin), or an interactive "instant". *)

(* Files are identified by an autonumber. *)
module File = struct
  type t = int

  (* The autonumber is just the length of a dynarray that records all the files seen up until now. *)
  let names : [ `File of string | `Other of string ] Dynarray.t = Dynarray.create ()
  let by_name : (string, t) Hashtbl.t = Hashtbl.create 20

  (* Create a new file.  A `File is a disk file with a fully-qualified name; an `Other is a command-line exec string, stdin, etc. *)
  let make (filename : [ `File of string | `Other of string ]) : t =
    let counter = Dynarray.length names in
    (* Only disk files can be looked up again by name. *)
    (match filename with
    | `File filename -> Hashtbl.add by_name filename counter
    | `Other _ -> ());
    Dynarray.add_last names filename;
    counter

  (* Look up a file's identifier by name. *)
  let get filename = Hashtbl.find by_name filename
  let to_string file = Dynarray.get names file
end

(* Interactive instants are also identified by an autonumber. *)
module Instant = struct
  type t = int

  let counter = ref (-1)

  let next () =
    counter := !counter + 1;
    !counter

  (* We can also step backwards through time (undo), but not past zero. *)
  let prev () =
    if !counter > 0 then (
      counter := !counter - 1;
      Some !counter)
    else None
end

module Origin = struct
  type t = Top | File of File.t | Instant of Instant.t

  let to_string = function
    | Top -> "T"
    | File f -> "F" ^ string_of_int f
    | Instant i -> string_of_int i

  (* The "current" origin is where new constants and metavariables will be created.  It could be the toplevel, a file, a present instant, or a "back in time" instant such as when filling a hole.  *)
  module Current = struct
    type t =
      | Top
      (* If we're in a file, we also remember whether holes are allowed. *)
      | File of File.t * bool
      | Present of Instant.t
      | Past of Instant.t
  end

  module S = Util.State.Make (Current)

  let () =
    S.register_printer (function
      | `Get -> Some "unhandled Origin.S.get effect"
      | `Set _ -> Some "unhandled Origin.S.set effect")

  let current () =
    match S.get () with
    | Top -> Top
    | File (file, _) -> File file
    | Past instant | Present instant -> Instant instant

  let holes_allowed () =
    match S.get () with
    | Top -> Error (`Other "toplevel")
    | File (_, true) -> Ok ()
    | File (i, false) -> Error (File.to_string i)
    | _ -> Ok ()

  (* We always start execution at the toplevel. *)
  let run f = S.run ~init:Top f

  (* Execute a new file, making it current, and then return to the previous current origin (wherever it was imported from).  The file object must have been created with File.make previously. *)
  let with_file ~holes_allowed file f = S.run ~init:(File (file, holes_allowed)) f

  (* Callbacks for changing instants, to grow or shrink all the Versioned Dynarrays. *)
  let nexts : (unit -> unit) list ref = ref []
  let prevs : (unit -> unit) list ref = ref []

  (* Callbacks for going back in time, to save the current state of versioned Dynarrays and restore it in case of failure. *)
  type rewinder = { wrap : 'a. Instant.t -> (unit -> 'a) -> unit -> 'a }

  let rewinds : rewinder list ref = ref []

  (* Switch to interactive mode.  Only works in top-level (after all files and exec-strings are completed). *)
  let set_interactive () =
    match S.get () with
    | Top ->
        List.iter (fun f -> f ()) !nexts;
        S.set (Present (Instant.next ()))
    | _ -> raise (Failure "Origin: can only switch to interactive mode from toplevel")

  (* Move to the next instant. *)
  let next () =
    match S.get () with
    | Present _ ->
        List.iter (fun f -> f ()) !nexts;
        S.set (Present (Instant.next ()))
    | _ -> raise (Failure "Origin: time can only pass in the present")

  (* Undo permanently to the previous instant. *)
  let undo () =
    match S.get () with
    | Present _ -> (
        List.iter (fun f -> f ()) !prevs;
        match Instant.prev () with
        | Some i ->
            S.set (Present i);
            `Ok
        | None -> `No_past)
    | Past _ -> raise (Failure "Origin: can't undo in the past")
    | _ -> `Not_interactive

  (* Every undoable command (e.g. def, axiom, notation, import, export, option) should be wrapped in this. *)
  let do_command f =
    match S.get () with
    | Present _ -> (
        (* We move to the next instant, if we're in interactive mode. *)
        next ();
        (* If the current command fails, we return to the previous instant. *)
        try f ()
        with e ->
          let _ = undo () in
          raise e)
    | _ -> f ()

  (* Similar, but always rewind the state.  Used for non-undoable commands like "echo" (which might still, say, allow holes, but such that any created holes should be immediately discarded afterwards). *)
  let do_command_then_undo f =
    match S.get () with
    | Present _ ->
        next ();
        Fun.protect f ~finally:(fun () ->
            let _ = undo () in
            ())
    | _ -> f ()

  (* Go back in time temporarily to a particular instant, run a callback command, and then return to the present.  The callback can modify the past state (of all versioned objects), with resulting effects on the present.  However, if it throws an exception, any such changes that it's made are discarded.  Used for commands like "solve" and "split". *)
  let rewind_command (instant : Instant.t) (f : unit -> 'a) : 'a =
    match S.get () with
    | Present _ ->
        S.run ~init:(Past instant) @@ fun () ->
        List.fold_left (fun g rewinder -> rewinder.wrap instant g) f !rewinds ()
    | _ -> raise (Failure "can only go back in time from the present")

  (* Similarly, but always behave as if an exception were thrown, so that no changes made in the past are permanent.  Used for commands like "echo" in the context of a hole, which might allow holes that should not be saved. *)
  let rewind_command_then_undo : type a. Instant.t -> (unit -> a) -> a =
   fun instant f ->
    (* In order to trigger the "rewinds", we manually raise an exception with the return value and then catch it.  We define the exception in a local module so it can be parametrized by the type parameter of this function. *)
    let module R = struct
      exception Rewind_then_undo of a
    end in
    try
      let _ = rewind_command instant (fun () -> raise (R.Rewind_then_undo (f ()))) in
      raise (Failure "rewind_then_undo: failed to raise")
    with R.Rewind_then_undo res -> res
end

(* A versioned object is a MUTABLE one that has a separate version for each origin.  A simple example is the autonumber that counts constant or metavariable identifiers.  A more complicated example is the scope or global environment of definitions. *)
module Versioned = struct
  type 'a t = {
    default : unit -> 'a;
    inherit_values : bool;
    top : 'a ref;
    files : 'a Dynarray.t;
    instants : 'a Dynarray.t;
  }

  (* Make a new versioned object with a given default value.  If inherit_values is true, then values for new files and the first instant are copied from top, while values for later instants are copied from the previous instant.  (This is appropriate for namespace scopes and notations.)  If inherit_values is false, then all new values are computed with the 'default', which is a function instead of a constant value so it can allocate new mutable values.  (This is appropriate for tables of constants and metavariables, whose identities already record their origins so we know which bucket to look for them in.) *)
  let make : type a. default:(unit -> a) -> inherit_values:bool -> a t =
   fun ~default ~inherit_values ->
    let top, files, instants = (ref (default ()), Dynarray.create (), Dynarray.create ()) in
    (* Add callbacks so that the instants array will grow or shrink as we go forwards or backwards in time.  These deal only with instants; the code for dealing with files is below in grow_files. *)
    Origin.nexts :=
      (fun () ->
        let v =
          if inherit_values then
            match Dynarray.find_last instants with
            | Some v -> v
            | None -> !top
          else default () in
        Dynarray.add_last instants v)
      :: !Origin.nexts;
    Origin.prevs := (fun () -> Dynarray.remove_last instants) :: !Origin.prevs;
    (* When rewinding to a past instant, we save the previous value in that instant, execute the code, and restore the original value in case of errors. *)
    Origin.rewinds :=
      {
        wrap =
          (fun i f () ->
            let v = Dynarray.get instants i in
            try f ()
            with e ->
              Dynarray.set instants i v;
              raise e);
      }
      :: !Origin.rewinds;
    { default; inherit_values; top; files; instants }

  (* If a files entry doesn't exist yet, we have to extend the array to make it long enough before setting the value.  This is the only way that the files array grows; we don't extend it automatically when new files are created. *)
  let grow_files : type a. a t -> File.t -> unit =
   fun x file ->
    while Dynarray.length x.files <= file do
      Dynarray.add_last x.files (if x.inherit_values then !(x.top) else x.default ())
    done

  (* Get the value of the object associated to a given origin.  If we are in the past, only instants before the current time are accessible. *)
  let get_at (x : 'a t) (i : Origin.t) : 'a option =
    try
      match i with
      | Top -> Some !(x.top)
      | File file ->
          grow_files x file;
          Some (Dynarray.get x.files file)
      | Instant instant -> (
          match Origin.S.get () with
          | Past now when instant > now -> None
          | _ -> Some (Dynarray.get x.instants instant))
    with Invalid_argument _ -> None

  (* Get the current value.  This is, of course, always possible. *)
  let get (x : 'a t) : 'a =
    match Origin.S.get () with
    | Top -> !(x.top)
    | File (file, _) ->
        grow_files x file;
        Dynarray.get x.files file
    | Present instant | Past instant -> Dynarray.get x.instants instant

  (* Set the current value. *)
  let set (x : 'a t) (v : 'a) : unit =
    match Origin.S.get () with
    | Top -> x.top := v
    | File (file, _) ->
        grow_files x file;
        Dynarray.set x.files file v
    | Present instant | Past instant -> Dynarray.set x.instants instant v

  (* Modify the current value. *)
  let modify (x : 'a t) (f : 'a -> 'a) : unit =
    match Origin.S.get () with
    | Top -> x.top := f !(x.top)
    | File (file, _) ->
        grow_files x file;
        Dynarray.set x.files file (f (Dynarray.get x.files file))
    | Present instant | Past instant ->
        Dynarray.set x.instants instant (f (Dynarray.get x.instants instant))

  (* Set the value of the object associated to a given file. *)
  let set_file (x : 'a t) (file : File.t) (v : 'a) : unit =
    grow_files x file;
    Dynarray.set x.files file v

  (* Fold over all the entries. *)
  let fold (x : 'a t) (f : 'acc -> 'a -> 'acc) (acc : 'acc) : 'acc =
    let acc = f acc !(x.top) in
    let acc = Dynarray.fold_left f acc x.files in
    Dynarray.fold_left f acc x.instants
end
