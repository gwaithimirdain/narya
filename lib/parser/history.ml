open Bwd
open Util
open Core
open Reporter
module Trie = Yuujinchou.Trie

(* History manages the global state, eternal state, and namespace scopes with a single state effect, and recording past versions of this state for "undo" purposes. *)

type moment = { global : Global.data; scope : Scope.t }

(* The length of 'past' is the number of undoable commands.  It starts out as empty.  The flag "undoing" indicates whether we're recording history and allowing undos; it should be set during interactive mode but not while loading files. *)
module Recorded = struct
  type t = { past : moment Bwd.t; present : moment; undoing : bool }
end

module S = State.Make (Recorded)

let run_empty : type a. (unit -> a) -> a =
 fun f ->
  S.run
    ~init:
      { past = Emp; present = { global = Global.empty; scope = Scope.empty () }; undoing = false }
  @@ fun () ->
  Global.try_with
    ~get:(fun () -> (S.get ()).present.global)
    ~set:(fun global -> S.modify (fun d -> { d with present = { d.present with global } }))
  @@ fun () ->
  Scope.run_with
    ~get:(fun () -> (S.get ()).present.scope)
    ~set:(fun scope -> S.modify (fun d -> { d with present = { d.present with scope } }))
    f

(* Every undoable command (e.g. def, axiom, notation, import, export, option) should be wrapped in this. *)
let do_command f =
  if (S.get ()).undoing then (
    (* First we save the state at the end of the previous command to the past, freeing up the present to be modified by the current command. *)
    S.modify (fun d -> { d with past = Snoc (d.past, d.present) });
    try f ()
    with e ->
      (* If the current command fails, we restore the state at the end of the previous command, including deleting any holes it created. *)
      S.modify (fun d ->
          match d.past with
          | Snoc (past, present) -> { d with past; present }
          | Emp -> fatal (Anomaly "nothing to unsave"));
      Eternity.filter_now ();
      raise e)
  else f ()

(* This is run *by* the 'undo' command.  Since 'undo' is not undoable, it is *not* wrapped in 'do_command'. *)
let undo n =
  (try
     S.modify (fun d ->
         if d.undoing then
           match Bwd_extra.remove d.past (n - 1) with
           | Snoc (past, present) -> { d with past; present }
           | Emp -> fatal Not_enough_to_undo
         else fatal (Forbidden_interactive_command "undo"))
   with Failure _ -> fatal Not_enough_to_undo);
  Eternity.filter_now ()

(* Undo ALL undoable (i.e. interactive) commands. *)
let undo_all () =
  S.modify (fun d ->
      if d.undoing then { d with past = Emp; present = Bwd_extra.head (Snoc (d.past, d.present)) }
      else fatal (Forbidden_interactive_command "undo"));
  Eternity.filter_now ()

(* Call this at the beginning of interactive mode *)
let start_undoing () = S.modify (fun d -> { d with undoing = true })
