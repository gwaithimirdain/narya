open Util
open Dim
open Reporter
open Norm
open Equal

(* This is a very bare-bones implementation of very simple subtyping.  We only allow subtyping between constants with no parameters (such as ℤ ≤ ℚ ≤ ℝ).  And there is no user interface for creating subtyping relations, so we don't check that the subtyping is valid (e.g. shared constructors or destructors); we trust the programmer to know what they're doing.  We store the subtypes in a state effect. *)

module S = State.Make (struct
  type t = unit Constant.Map.t Constant.Map.t
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled Subtype get effect"
    | `Set _ -> Some "unhandled Subtype set effect")

let add subtype supertype =
  match (Global.find subtype, Global.find supertype) with
  | (UU subdim, _), (UU superdim, _) -> (
      match (D.compare_zero subdim, D.compare_zero superdim) with
      | Zero, Zero ->
          S.modify
            (Constant.Map.update subtype (function
              | Some m -> Some (Constant.Map.add supertype () m)
              | None -> Some (Constant.Map.add supertype () Constant.Map.empty)))
      (* This shouldn't happen, since higher-dimensional universes aren't types unless instantiated. *)
      | _ -> fatal (Anomaly "higher-dimensional universe in subtyping"))
  | (Inst _, _), _ | _, (Inst _, _) ->
      fatal (Unimplemented "subtyping between higher-dimensional types")
  | (Pi _, _), _ | _, (Pi _, _) -> fatal (Unimplemented "subtyping relations with parameters")
  | _ -> fatal (Anomaly "non-type in subtyping")

let run ?(init = Constant.Map.empty) = S.run ~init

let subtype_of ctx subtype supertype =
  let subty, superty =
    Reporter.try_with ~fatal:(fun _ -> (None, None)) @@ fun () ->
    (Some (view_type subtype "subtype_of"), Some (view_type supertype "supertype_of")) in
  let open Monad.Ops (Monad.Maybe) in
  match (subty, superty) with
  | ( Some (Canonical (Const { name = subname; ins = subins }, _, _, subargs)),
      Some (Canonical (Const { name = supername; ins = superins }, _, _, superargs)) )
    when Option.is_some
         @@ let* m = Constant.Map.find_opt subname (S.get ()) in
            let* () = Constant.Map.find_opt supername m in
            (* Higher-dimensional versions of subtypes are also subtypes, as long as they are instantiated at equal tubes. *)
            let* () = equal_ins subins superins in
            equal_tyargs ctx subargs superargs -> Ok ()
  (* If there is no subtyping relaton, we revert to checking type equality. *)
  | _ -> equal_val ctx subtype supertype
