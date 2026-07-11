open Util
open Tbwd
open Dim
open Modal
open Tctx
open Reporter
open Value
open Readback
open Norm

(* Degenerating contexts (for higher inductive and coinductive types).  The degeneracy of a context by a dimension k is a context in which all the n-cubes of variables have been replaced by (k+n)-cubes, whose types are degenerate versions of those in the original context.  Thus, while its raw length is the same, its checked length has k added to all the dimensions.  There is a canonical k-dimensional substitution (environment) from the degenerated context to the original one, which is the universal such substitution exhibiting the degenerated context as a power/cotensor in the dimension-enriched category of contexts.  (The universal property of this power/cotensor is implemented by the Shift operation on environments/substitutions.)

   You might naively think that we could build the degenerated context by iterating through the original one and applying "act" to all the types.  However, the degenerated context has *more level variables* than the original context does, and we need to create these variables and ensure that they appear in all the later types as needed.  Thus, it seems that we really do have to do an eval-readback cycle. *)

module Ordered = struct
  open Ctx.Ordered

  let degenerate_binding : type dom modality mode k l n kn ax b.
      int ->
      k D.t ->
      l D.t ->
      (k, n, kn) D.plus ->
      (dom, modality, mode, k, l) Modality.filter_dim ->
      (dom, modality, mode, n, n) Modality.filter_dim ->
      (n, dom Binding.t) CubeOf.t ->
      (* Because the values and types of variables in one cube can refer to other variables in the same cube, we need to be given the extended context with this binding included at the end in order to readback. *)
      (mode, ax, (b, (modality, n) dim_entry) snoc) t ->
      (* But we are building the degenerating environment as we go, so we don't have the extended version of that yet. *)
      (mode, l, b) env ->
      (kn, dom Binding.t) CubeOf.t * (kn, (dom, kinetic) value) CubeOf.t =
   fun i k l k_n filter filtered xs ctx env ->
    let kn = D.plus_out k k_n in
    let ctx = Ctx.of_ordered ctx in
    let modality = Modality.filter_modality filter in
    let (Locked (plus, lctx)) = Ctx.lock ctx modality in
    let readbacks =
      CubeOf.mmap
        {
          map =
            (fun _ [ x ] ->
              let nf = Binding.value x in
              match Binding.level x with
              | None -> (Some (readback_nf lctx nf), readback_val lctx nf.ty)
              | Some _ -> (None, readback_val lctx nf.ty));
        }
        [ xs ] in
    let j = ref 0 in
    let xstbl = Hashtbl.create 20 in
    let newxs =
      CubeOf.build kn
        {
          build =
            (fun fab ->
              (* At each step we need to re-build a partially extended environment containing the values for smaller faces that we have already evaluated, in order to evaluate the term for this face. *)
              let prev_vals =
                CubeOf.build kn
                  {
                    build =
                      (fun fab' ->
                        match Hashtbl.find_opt xstbl (SFace_of fab') with
                        | Some x -> ready (Val x.tm)
                        | None ->
                            defer (Modality.src modality) (fun () ->
                                fatal (Anomaly "variable out of scope in degenerate_binding")));
                  } in
              let env = Ext { env; plus = k_n; values = `Lazy prev_vals; filter; filtered } in
              let lenv = Key (env, Modalcell.id modality, plus) in
              let (SFace_of_plus (_, fa, fb)) = sface_of_plus k_n fab in
              let alenv =
                act_env lenv
                  (opt_op_of_opt_sface
                     (comp_opt_sface (Modality.sface_of_filter l filter) (opt_of_sface fa))) in
              let m = dom_sface fb in
              match CubeOf.find readbacks fb with
              | None, ty ->
                  let level = (i, !j) in
                  j := !j + 1;
                  let ty = Norm.eval_term alenv ty in
                  let ty =
                    inst ty
                      (TubeOf.build D.zero
                         (D.zero_plus (dom_sface fa))
                         {
                           build =
                             (fun fc ->
                               let (Plus l_m) = D.plus m in
                               Hashtbl.find xstbl
                                 (SFace_of
                                    (sface_plus_sface
                                       (comp_sface fa (sface_of_tface fc))
                                       k_n l_m fb)));
                         }) in
                  let v = { tm = var modality level ty; ty } in
                  Hashtbl.add xstbl (SFace_of fab) v;
                  Binding.make (Some level) v
              | Some tm, ty ->
                  (* Incrementing the level isn't really necessary since we aren't going to use it in this case, but we do it anyway for consistency. *)
                  j := !j + 1;
                  let tm = Norm.eval_term alenv tm in
                  let ty = Norm.eval_term alenv ty in
                  let ty =
                    inst ty
                      (TubeOf.build D.zero
                         (D.zero_plus (dom_sface fa))
                         {
                           build =
                             (fun fc ->
                               let (Plus l_m) = D.plus m in
                               Hashtbl.find xstbl
                                 (SFace_of
                                    (sface_plus_sface
                                       (comp_sface fa (sface_of_tface fc))
                                       k_n l_m fb)));
                         }) in
                  let v = { tm; ty } in
                  Hashtbl.add xstbl (SFace_of fab) v;
                  Binding.make None v);
        } in
    let newvals = CubeOf.mmap { map = (fun _ [ v ] -> (Binding.value v).tm) } [ newxs ] in
    (newxs, newvals)

  type (_, _, _, _) degctx =
    | Degctx :
        ('k, 'b, 'kb, 'mode) plusmap * ('mode, 'a, 'kb) t * ('mode, 'k, 'b) env
        -> ('mode, 'a, 'b, 'k) degctx

  (* TODO: Short-circuit if k=0. *)
  let rec degenerate : type mode a b l. (mode, a, b) t -> l D.t -> (mode, a, b, l) degctx =
   fun ctx l ->
    match ctx with
    | Emp mode ->
        Degctx
          ( Suc (Zero (Eq Unit), Inject (Plus_proj mode), Suc (Zero, Proj mode)),
            Emp mode,
            Emp (mode, l) )
    | Snoc (ctx', entry, ax) ->
        let (Degctx (kb, newctx', env)) = degenerate ctx' l in
        let mn = Ctx.dim_entry entry in
        let modality = Ctx.modality_entry entry in
        let (Has_filter filter_k_l) = Modality.filter modality l in
        let k = Modality.filtered l filter_k_l in
        let (Plus k_mn) = D.plus mn in
        let newentry, newenv, filter_kmn, filter_mn =
          match entry with
          | Vis { hasfields = Has_fields; _ } ->
              fatal (Anomaly "attempt to degenerate a context containing illusory variables")
          | Vis
              {
                dim;
                filter = filter_mn;
                plusdim;
                vars;
                bindings;
                hasfields = No_fields;
                fields;
                fplus;
              } ->
              let (Plus km) = D.plus dim in
              let plusdim = D.plus_assocl km plusdim k_mn in
              let bindings, newval =
                degenerate_binding (length newctx') k l k_mn filter_k_l filter_mn bindings ctx env
              in
              let hasfields = Term.No_fields in
              let filter_kmn =
                Modality.filter_plus k_mn k_mn (Modality.filter_idempotent filter_k_l) filter_mn
              in
              ( Ctx.Vis
                  {
                    dim = D.plus_out k km;
                    filter = filter_kmn;
                    plusdim;
                    vars;
                    bindings;
                    hasfields;
                    fields;
                    fplus;
                  },
                Ext
                  {
                    env;
                    plus = k_mn;
                    filter = filter_k_l;
                    filtered = filter_mn;
                    values = `Ok newval;
                  },
                filter_kmn,
                filter_mn )
          | Invis { filter = filter_mn; bindings = xs } ->
              let newxs, newval =
                degenerate_binding (length newctx') k l k_mn filter_k_l filter_mn xs ctx env in
              let filter_kmn =
                Modality.filter_plus k_mn k_mn (Modality.filter_idempotent filter_k_l) filter_mn
              in
              ( Invis { filter = filter_kmn; bindings = newxs },
                Ext
                  {
                    env;
                    plus = k_mn;
                    filter = filter_k_l;
                    filtered = filter_mn;
                    values = `Ok newval;
                  },
                filter_kmn,
                filter_mn ) in
        Degctx
          ( Suc
              ( kb,
                Inject (Plus_dim (k_mn, filter_mn, filter_k_l)),
                Suc (Zero, Dim (D.plus_out k k_mn, filter_kmn)) ),
            Snoc (newctx', newentry, ax),
            newenv )
    | Lock (ctx, lock) ->
        let (Degctx (kb, newctx, env)) = degenerate ctx l in
        Degctx
          ( Suc (kb, Inject (Plus_lock lock), Suc (Zero, Lock lock)),
            Lock (newctx, lock),
            Key
              ( env,
                Modalcell.id (Modality.of_gen lock),
                Plus_lock
                  ( Suc (Zero (Eq (Ctx.Ordered.mode ctx)), Lock_lock lock, Suc (Zero, Lock lock)),
                    Suc (Zero, Lock lock) ) ) )
end

type (_, _, _, _) degctx =
  | Degctx :
      ('k, 'b, 'kb, 'mode) plusmap * ('mode, 'a, 'kb) Ctx.t * ('mode, 'k, 'b) env
      -> ('mode, 'a, 'b, 'k) degctx

let degctx : type mode a b k. (mode, a, b) Ctx.t -> k D.t -> (mode, a, b, k) degctx =
 fun (Permute { perm; ctx; level; _ }) k ->
  let (Degctx (kb, newctx, env)) = Ordered.degenerate ctx k in
  Degctx (kb, Permute { perm; env = Ctx.Ordered.env newctx; level; ctx = newctx }, env)
