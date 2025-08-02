(* This module should not be opened, but used qualified. *)

open Util
open Term
open Status

(* Holes also store their status, vars, and tightness intervals so we can tell whether a term would parse to replace them.  Note that a 'status' contains a functional value, so a 'holedata' cannot be marshaled. *)
type ('a, 'b, 's) hole = {
  status : ('b, 's) status;
  vars : (string option, 'a) Bwv.t;
  li : No.interval;
  ri : No.interval;
  parametric : [ `Parametric | `Nonparametric ];
}

type ('a, 'b, 's) t = {
  energy : 's energy;
  tm : [ `Defined of ('b, 's) term | `Axiom | `Undefined ];
  (* If a metavariable were "lifted" to top level with pi-types, then its type would be the pi-type over its context of the type in that context.  We instead store them separately without doing the lifting. *)
  termctx : ('a, 'b) termctx;
  ty : ('b, kinetic) term;
}

(* Define or redefine a metavariable. *)
let define : type a b s. (b, s) term -> (a, b, s) t -> (a, b, s) t =
 fun tm m -> { m with tm = `Defined tm }
