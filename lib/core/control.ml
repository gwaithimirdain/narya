(* This module should not be opened, but used qualified. *)

open Bwd
open Origin

(* Attempts at doing something that might be abandoned, such as typechecking a term in one way that, if it fails, will be redone in another way.  When an attempt is abandoned, both its effects on the global state (see Origin.speculate) and the diagnostics it reported (see Reporter.collect) belong to it, so they are discarded along with it.  Each of the wrappers here combines the two, according to its own notion of when an attempt is abandoned. *)

(* An attempt can be abandoned by raising this exception, which is for nonlocal control flow rather than error reporting (see Reporter.Backtrack). *)
type backtrack = Reporter.backtrack = ..

exception Backtrack = Reporter.Backtrack

(* Run a callback that should fail if it reports any mortal errors (see Reporter.capture).  If it fails, its effects on the global state are backtracked. *)
let capture (f : unit -> 'a) : ('a, Reporter.pending Bwd.t) Result.t =
  Origin.speculate (fun () -> Reporter.capture f)

(* Like [capture], but in the case of success the emitted diagnostics are returned to the caller rather than released (see Reporter.speculate). *)
let speculate (f : unit -> 'a) : ('a * Reporter.pending Bwd.t, Reporter.pending Bwd.t) Result.t =
  Origin.speculate (fun () -> Reporter.speculate f)

(* Like [speculate], but its effects on the global state are always backtracked, even if it succeeds, so that only its result and its diagnostics are retained.  This is for an attempt whose result is used only to decide what to report. *)
let trial (f : unit -> 'a) : ('a * Reporter.pending Bwd.t, Reporter.pending Bwd.t) Result.t =
  Origin.speculate_discard (fun () -> Reporter.speculate f)
