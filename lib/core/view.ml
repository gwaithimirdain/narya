open Dim
open Value
open Reporter

(* A "view" is the aspect of a type or term that we match against to determine its behavior.  A view of a term is just another term, but in WHNF.  A view of a type is either a canonical type (data or codata) or a neutral, either fully instantiated at the correct dimension. *)

type 'mode view_type =
  | Canonical :
      ('mode head * ('mode, 'm, 'n) canonical * ('mn, 'm, 'n) insertion * (D.zero, 'mn, 'mn, 'mode normal) TubeOf.t)
      -> 'mode view_type
  | Neutral : ('mode head * ('mode, noninst) apps * (D.zero, 'k, 'k, 'mode normal) TubeOf.t) -> 'mode view_type

type term_viewer_type = { view : 'mode. ('mode, kinetic) value -> ('mode, kinetic) value }

let term_viewer : term_viewer_type ref =
  ref { view = (fun _ -> fatal (Anomaly "term_viewer not set (load Norm)")) }

type type_viewer_type = {
  view : 'mode. ?severity:Asai.Diagnostic.severity -> ('mode, kinetic) value -> string -> 'mode view_type;
}

let type_viewer : type_viewer_type ref =
  ref { view = (fun ?severity:_ _ _ -> fatal (Anomaly "type_viewer not set (load Norm)")) }

type force_eval_type = { force : 'mode 's. ('mode, 's) lazy_eval -> ('mode, 's) evaluation }

let eval_forcer : force_eval_type ref =
  ref { force = (fun _ -> fatal (Anomaly "force_eval not set (load Norm)")) }

let view_term tm = !term_viewer.view tm
let view_type : type mode. ?severity:Asai.Diagnostic.severity -> (mode, kinetic) value -> string -> mode view_type =
 fun ?severity ty msg -> !type_viewer.view ?severity ty msg
let force_eval : type mode s. (mode, s) lazy_eval -> (mode, s) evaluation = fun tm -> !eval_forcer.force tm
