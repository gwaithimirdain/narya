(* Unification: solving unification metavariables by comparing them with other values.  For now, we only implement the simplest case. *)

open Dim
open Term
open Value
open Readback

(* Try to solve a unification metavariable u with a value v, which are being compared in a context, at a type if known.  We can do this if u is a neutral unification metavariable with no arguments, an identity insertion, and an environment that is a renaming (see Readback.renamed_ctx), and v reads back in the corresponding renamed context without containing u (see Readback.Unifying).  Then the solution, substituted into u's environment, is v. *)
let try_solve : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, kinetic) value option ->
    bool =
 fun ctx u v ty ->
  match u with
  | Neu { head = Live (Meta { meta; kind = Unif_meta unif; env; ins }); args = Emp; ty = uty; _ }
    -> (
      match (is_id_ins ins, v) with
      | None, _ -> false
      (* Two occurrences of the same metavariable are compared by their environments instead. *)
      | Some _, Neu { head = Live (Meta { meta = meta'; _ }); _ }
        when match Meta.compare meta meta' with
             | Eq -> true
             | Neq -> false -> false
      | Some _, _ -> (
          (Global.unif_status meta unif = `Unsolved && Global.unif_assignable meta)
          &&
          match renamed_ctx ctx env (Global.unif_ctx meta) with
          | None -> false
          | Some (Renamed_ctx rctx) -> (
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
              (* We read back v at the type of u, which has been substituted by its environment and hence lives in the current context like v. *)
              match readback_unif_solution meta rctx v (Lazy.force uty) with
              | Some tm ->
                  Global.solve_unif meta tm;
                  true
              | None -> false)))
  | _ -> false

let install () =
  Equal.solver := { solve = (fun ctx x y ty -> try_solve ctx x y ty || try_solve ctx y x ty) }
