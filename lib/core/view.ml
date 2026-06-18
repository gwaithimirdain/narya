open Util
open Dim
open Variables
open Value
open Reporter

(* A "view" is the aspect of a type or term that we match against to determine its behavior.  A view of a term is just another term, but in WHNF.  A view of a type is either a canonical type (data or codata) or a neutral, either fully instantiated at the correct dimension. *)

type 'mode view_type =
  | Canonical :
      ('mode head
      * ('mode, 'm, 'n) canonical
      * ('mn, 'm, 'n) insertion
      * (D.zero, 'mn, 'mn, 'mode normal) TubeOf.t)
      -> 'mode view_type
  | Neutral :
      ('mode head * ('mode, noninst) apps * (D.zero, 'k, 'k, 'mode normal) TubeOf.t)
      -> 'mode view_type

type term_viewer_type = { view : 'mode. ('mode, kinetic) value -> ('mode, kinetic) value }

let term_viewer : term_viewer_type ref =
  ref { view = (fun _ -> fatal (Anomaly "term_viewer not set (load Norm)")) }

type type_viewer_type = {
  view :
    'mode. ?severity:Asai.Diagnostic.severity -> ('mode, kinetic) value -> string -> 'mode view_type;
}

let type_viewer : type_viewer_type ref =
  ref { view = (fun ?severity:_ _ _ -> fatal (Anomaly "type_viewer not set (load Norm)")) }

type force_eval_type = { force : 'mode 's. ('mode, 's) lazy_eval -> ('mode, 's) evaluation }

let eval_forcer : force_eval_type ref =
  ref { force = (fun _ -> fatal (Anomaly "force_eval not set (load Norm)")) }

let view_term tm = !term_viewer.view tm

let view_type : type mode.
    ?severity:Asai.Diagnostic.severity -> (mode, kinetic) value -> string -> mode view_type =
 fun ?severity ty msg -> !type_viewer.view ?severity ty msg

let force_eval : type mode s. (mode, s) lazy_eval -> (mode, s) evaluation =
 fun tm -> !eval_forcer.force tm

(* Extract the variable-name hints associated to a type value, if it is a canonical datatype or codatatype with such hints declared.  This is used when generating names to display anonymous variables of that type.  We can't use view_type, since it requires higher-dimensional types to be fully instantiated, whereas the domains of a higher-dimensional pi-type are not.  Instead we force the value of the neutral directly.  Since this only affects display, if anything goes wrong (e.g. the value is not actually a type) we just return no hints rather than failing. *)
let hints_of_ty : type mode. (mode, kinetic) value -> hints =
 fun ty ->
  Reporter.try_with ~fatal:(fun _ -> no_hints) @@ fun () ->
  match view_term ty with
  | Neu { value; _ } -> (
      match force_eval value with
      | Val (Canonical { canonical = Data { hints; _ }; _ }) -> hints
      | Val (Canonical { canonical = Codata { hints; _ }; _ }) -> hints
      | _ -> no_hints)
  | _ -> no_hints

(* Convert a possibly-absent user-supplied variable name to a binder_name, attaching hints derived from the type of the variable if it is anonymous. *)
let hinted : type mode. string option -> (mode, kinetic) value -> binder_name =
 fun x ty ->
  match x with
  | Some x -> `Named x
  | None -> `Anon (hints_of_ty ty)

(* Refresh the hints of the anonymous variables in a cube of binder names, deriving them from a matching cube of their types, such as the domains of a pi-type. *)
let fill_hints : type mode mn. (mn, (mode, kinetic) value) CubeOf.t -> mn variables -> mn variables
    =
 fun doms vars ->
  match vars with
  | Variables
      (type m n f)
      ((m, m_n, xs) : m D.t * (m, n, mn) D.plus * (N.zero, n, binder_name, f) NICubeOf.t) ->
      let fill : type left k.
          (k, n) sface -> (left, k, binder_name) NFamOf.t -> (left, k, binder_name) NFamOf.t =
       fun fb (NFamOf x) ->
        match x with
        | `Named _ -> NFamOf x
        | `Anon _ ->
            let (Plus m_k) = D.plus (dom_sface fb) in
            NFamOf (`Anon (hints_of_ty (CubeOf.find doms (plus_sface m m_n m_k fb)))) in
      Variables (m, m_n, NICubeOf.map { map = (fun fb x -> fill fb x) } xs)
