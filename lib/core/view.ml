open Dim
open Value
open Reporter

(* A "view" is the aspect of a type or term that we match against to determine its behavior.  A view of a term is just another term, but in WHNF.  A view of a type is either a canonical type (data or codata) or a neutral, either fully instantiated at the correct dimension. *)

type view_type =
  | Canonical :
      (head * ('m, 'n) canonical * ('mn, 'm, 'n) insertion * (D.zero, 'mn, 'mn, normal) TubeOf.t)
      -> view_type
  | Neutral : (head * noninst apps * (D.zero, 'k, 'k, normal) TubeOf.t) -> view_type

let term_viewer : (kinetic value -> kinetic value) ref =
  ref (fun _ -> fatal (Anomaly "term_viewer not set (load Norm)"))

let type_viewer : (?severity:Asai.Diagnostic.severity -> kinetic value -> string -> view_type) ref =
  ref (fun ?severity:_ _ _ -> fatal (Anomaly "type_viewer not set (load Norm)"))

type force_eval_type = { force : 's. 's lazy_eval -> 's evaluation }

let eval_forcer : force_eval_type ref =
  ref { force = (fun _ -> fatal (Anomaly "force_eval not set (load Norm)")) }

let view_term tm = !term_viewer tm
let view_type ty = !type_viewer ty
let force_eval : type s. s lazy_eval -> s evaluation = fun tm -> !eval_forcer.force tm
