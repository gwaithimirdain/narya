(* Unification: solving unification metavariables by comparing them with other values.  For now, we only implement the simplest case. *)

open Util
open Dim
open Reporter
open Term
open Value
open Norm
open Readback

(* Try to solve a unification metavariable u with a value v, which are being compared in a context, at a type if known.  We can do this if u is a neutral unification metavariable with an identity insertion, and an environment and arguments that are a renaming (see Readback.renamed_ctx), and v reads back in the corresponding renamed context without containing u or any undefined variable (see Readback.Unifying).  Then the solution, substituted into u's environment, is v. *)
let try_solve : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, kinetic) value option ->
    bool =
 fun ctx u v ty ->
  match u with
  | Neu { head = Live (Meta { meta; kind = Unif_meta unif as kind; env; ins }); args; ty = uty; _ }
    -> (
      match (is_id_ins ins, arg_spine args, v) with
      | None, _, _ | _, None, _ -> false
      (* Two occurrences of the same metavariable are compared by their environments and arguments instead. *)
      | Some _, Some _, Neu { head = Live (Meta { meta = meta'; _ }); _ }
        when match Meta.compare meta meta' with
             | Eq -> true
             | Neq -> false -> false
      | Some _, Some Eq, _ -> (
          (Global.unif_status meta unif = `Unsolved && Global.unif_assignable meta)
          &&
          let mty = Global.meta_ty meta kind in
          match renamed_ctx meta ctx env args mty (Global.unif_ctx meta) v with
          | None -> false
          | Some (Renamed_ctx { ctx = rctx; check_type; wrap; contracted }) -> (
              (* If we don't know the type at which they are being compared, we must check that the type of v is that of u. *)
              let typed =
                match ty with
                | Some _ -> true
                | None -> (
                    match v with
                    | Neu { ty = vty; _ } -> (
                        match Equal.equal_val ctx (Lazy.force vty) (Lazy.force uty) with
                        | Ok () -> true
                        | Error _ -> false)
                    | _ -> false) in
              typed
              &&
              (* If we can eta-contract, we do.  Otherwise, we read back v at the type of u, which has been substituted by its environment and arguments and hence lives in the current context like v. *)
              let solution =
                match List.find_map (fun attempt -> attempt ()) contracted with
                | Some _ as tm -> tm
                | None ->
                    Option.map wrap
                      (readback_unif_solution meta rctx ~check_type v (Lazy.force uty)) in
              match solution with
              | Some tm ->
                  Global.solve_unif meta tm;
                  true
              | None -> false)))
  | _ -> false

(* A metavariable that is projected from, perhaps after being applied to some arguments, has to be solved by a tuple, since we can only get information about one field from the projection, and the other fields have to be left unknown.  This is always correct, by eta-conversion, so it doesn't affect whether the solution is most general; but it does create more metavariables, so we do it only when solving an equation that requires it.  To avoid having to duplicate the logic for typechecking tuples, particularly regarding modal fields (whose components live in a locked context, and possibly a different mode), we do this by constructing a raw term out of abstractions, tuples, and placeholders, and typechecking it at the type of the metavariable.  Since typechecking comes later, we record here just the shape of the term, consisting of an abstraction for each argument (with a name, and whether it is a cube abstraction) and a tuple for each projection (with all the field names and the one that continues).  There is no need for a final sequence of abstractions, since the metavariables created for the tuple components can just be applied to the same arguments. *)
type expansion = Abs of string option * bool | Tuple of string list * string

type expander = {
  expand :
    'mode 'a 'b.
    ('mode, 'a, 'b) Ctx.t -> ('mode, kinetic) value -> expansion list -> ('mode, 'b, kinetic) term;
}

let expander : expander ref =
  ref { expand = (fun _ _ _ -> fatal (Anomaly "unification not installed")) }

(* Compute the shape of the expansion needed by a metavariable with an application spine, given the value of the metavariable with no spine, if it is possible.  We replay the spine on that value in order to be able to compute the type at each point. *)
let expansion_shape : type hmode mode any.
    (hmode, kinetic) value -> (hmode, mode, any, live) apps -> expansion list option =
 fun head args ->
  let exception Stuck in
  let tyof : type m. (m, kinetic) value -> m View.view_type = function
    | Neu { ty; _ } -> view_type ~severity:Asai.Diagnostic.Error (Lazy.force ty) "expansion_shape"
    | _ -> raise_notrace Stuck in
  let rec go : type m any. (hmode, m, any, live) apps -> (m, kinetic) value * expansion list =
    function
    | Emp -> (head, [])
    | Snoc (args, entry) ->
        let cur, shape = go args in
        let shape =
          match entry with
          | Arg (_, xs, _) -> (
              match tyof cur with
              | Canonical (_, Pi { x; _ }, _, _) ->
                  let cube =
                    match D.compare_zero (CubeOf.dim xs) with
                    | Zero -> false
                    | Pos _ -> true in
                  Abs (option_of_binder_name (top_variable x), cube) :: shape
              | _ -> raise_notrace Stuck)
          | Field (_, fld, _, _) -> (
              match tyof cur with
              | Canonical (_, Codata { eta = Eta; fields; _ }, _, _) ->
                  let names =
                    Bwd_extra.to_list_map
                      (fun (Term.CodatafieldAbwd.Entry (f, _)) -> Field.to_string f)
                      fields in
                  Tuple (names, Field.to_string fld) :: shape
              | _ -> raise_notrace Stuck)
          | Inst _ -> raise_notrace Stuck in
        let (Val next) = app_eval_entry (Val cur) entry in
        (next, shape) in
  let rec trim = function
    | Abs _ :: shape -> trim shape
    | shape -> shape in
  try
    match trim (snd (go args)) with
    | [] -> None
    | shape -> Some (List.rev shape)
  with Stuck -> None

(* Expand a unification metavariable that is projected from, and then compare the result to the other value. *)
let try_expand : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, kinetic) value option ->
    bool =
 fun ctx u v ty ->
  match u with
  | Neu { head = Live (Meta { meta; kind = Unif_meta unif as kind; env; ins }); args; _ } -> (
      match (is_id_ins ins, arg_spine args, v) with
      | None, _, _ | _, Some _, _ -> false
      | _, _, Neu { head = Live (Meta { meta = meta'; _ }); _ }
        when match Meta.compare meta meta' with
             | Eq -> true
             | Neq -> false -> false
      | Some _, None, _ -> (
          (Global.unif_status meta unif = `Unsolved && Global.unif_assignable meta)
          &&
          let head = eval_term env (Meta (meta, kind, Kinetic)) in
          Reporter.discard_errors ~fallback:(fun () -> false) @@ fun () ->
          match expansion_shape head args with
          | None -> false
          | Some shape -> (
              let mctx = Global.unif_ctx meta in
              let mty = eval_term (Ctx.env mctx) (Global.meta_ty meta kind) in
              Global.solve_unif meta (!expander.expand mctx mty shape);
              (* Now u has a value, whose head is a metavariable created for a tuple component, so we can try again to solve that. *)
              let result =
                match ty with
                | Some ty -> Equal.equal_at ctx (view_term u) v ty
                | None -> Equal.equal_val ctx (view_term u) v in
              match result with
              | Ok () -> true
              | Error _ -> false)))
  | _ -> false

let install (expand : expander) =
  expander := expand;
  Equal.solver :=
    {
      solve =
        (fun ctx x y ty ->
          (* We prefer not to expand, if the other side can be solved directly. *)
          try_solve ctx x y ty
          || try_solve ctx y x ty
          || try_expand ctx x y ty
          || try_expand ctx y x ty);
    }
