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

(* Run a callback that might be abandoned by raising a [Backtrack], holding back the diagnostics it reports until it finishes and then passing them on as if nothing had happened.  If it is abandoned by a [Backtrack], they are discarded along with it (see Reporter.collect).  If it raises any exception, its effects on the global state are backtracked. *)
let backtrackable (f : unit -> 'a) : 'a =
  Reporter.uncollect (Reporter.collect (fun () -> Origin.speculate_exn f))

(* Run a callback that might fail with a fatal error from which the caller recovers by redoing its work in a different way, holding back the diagnostics it reports.  If it raises any exception, its effects on the global state are backtracked.  If that was a fatal error for which [recover] supplies a recovery, the diagnostics are discarded along with the failed attempt and the recovery is run instead.  Otherwise they are passed on as if nothing had happened. *)
let recovering ~(recover : Reporter.Code.t Asai.Diagnostic.t -> (unit -> 'a) option)
    (f : unit -> 'a) : 'a =
  match Reporter.collect (fun () -> Origin.speculate_exn f) with
  | (Error d, _) as result -> (
      match recover d with
      | Some g -> g ()
      | None -> Reporter.uncollect result)
  | result -> Reporter.uncollect result
