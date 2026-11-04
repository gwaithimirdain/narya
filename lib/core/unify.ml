(* Unification: solving unification metavariables by comparing them with other values.  For now, we only implement the simplest case. *)

open Dim
open Term
open Value
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

let install () =
  Equal.solver := { solve = (fun ctx x y ty -> try_solve ctx x y ty || try_solve ctx y x ty) }
