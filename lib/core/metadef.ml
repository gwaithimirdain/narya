(* This module should not be opened, but used qualified. *)

open Util
open Term
open Status

(* Holes also store their status, vars, and tightness intervals so we can tell whether a term would parse to replace them.  Note that a 'status' contains a functional value, so a 'holedata' cannot be marshaled. *)
type ('mode, 'a, 'b, 's) hole = {
  status : ('mode, 'b, 's) status;
  vars : (string option, 'a) Bwv.t;
  li : No.interval;
  ri : No.interval;
  parametric : [ `Parametric | `Nonparametric ];
}

type ('mode, 'a, 'b, 's) t = {
  energy : 's energy;
  tm : [ `Defined of ('mode, 'b, 's) term | `Axiom | `Undefined ];
  (* If a metavariable were "lifted" to top level with pi-types, then its type would be the pi-type over its context of the type in that context.  We instead store them separately without doing the lifting. *)
  termctx : ('mode, 'a, 'b) termctx;
  ty : ('mode, 'b, kinetic) term;
}

(* Define or redefine a metavariable. *)
let define : type mode a b s. (mode, b, s) term -> (mode, a, b, s) t -> (mode, a, b, s) t =
 fun tm m -> { m with tm = `Defined tm }
