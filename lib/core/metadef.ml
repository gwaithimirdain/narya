(* This module should not be opened, but used qualified. *)

open Util
open Term
open Status

(* Holes also store their status, vars, and tightness intervals so we can tell whether a term would parse to replace them.  They also store the set of constants that were being defined when the hole was created, so that when the hole is solved, occurrences of those constants in the solution can be detected as recursive.  Note that a 'status' contains a functional value, so a 'holedata' cannot be marshaled. *)
type ('mode, 'a, 'b, 's) hole = {
  status : ('mode, 'b, 's) status;
  vars : (string option, 'a) Bwv.t;
  li : No.interval;
  ri : No.interval;
  parametric : [ `Parametric | `Nonparametric ];
  beingdefined : unit Constant.Map.t;
}

type ('mode, 'a, 'b, 's) t = {
  energy : 's energy;
  tm : [ `Defined of ('mode, 'b, 's) term | `Axiom | `Undefined ];
  (* If a metavariable were "lifted" to top level with pi-types, then its type would be the pi-type over its context of the type in that context.  We instead store them separately without doing the lifting. *)
  termctx : ('mode, 'a, 'b) termctx;
  ty : ('mode, 'b, kinetic) term;
  (* Whether the definition contains occurrences of constants that were being defined when the metavariable was created.  Meaningful only once the metavariable is defined; consulted when chasing the recursion verdicts of datatypes whose constructor types contain holes. *)
  recursion : Positivity.recursion;
}

(* Define or redefine a metavariable, recording the recursion verdict of its definition if one is supplied. *)
let define : type mode a b s.
    ?recursion:Positivity.recursion -> (mode, b, s) term -> (mode, a, b, s) t -> (mode, a, b, s) t =
 fun ?recursion tm m ->
  { m with tm = `Defined tm; recursion = Option.value recursion ~default:m.recursion }
