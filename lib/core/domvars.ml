open Bwd
open Util
open Modal
open Reporter
open Dim
open Tctx
open Term
open Value
open Norm

(* To typecheck a lambda, do an eta-expanding equality check, check pi-types for equality, or read back a pi-type or a term at a pi-type, we must create one new variable for each argument in the boundary.  Sometimes we need these variables as values and other times as normals.  The function dom_vars creates these variables and returns them in two cubes.  It, and the function ext_pi below that follows from it, are in a separate file because it depends on Inst and Ctx and is used in Equal, Readback, and Check, and doesn't seem to be placed naturally in any of those files. *)

let dom_vars : type dom modality mode m a b.
    (mode, a, b) Ctx.t ->
    (dom, modality, mode) Modality.t ->
    (m, (dom, kinetic) value) CubeOf.t ->
    (m, (dom, kinetic) value) CubeOf.t * (m, dom Ctx.Binding.t) CubeOf.t =
 fun ctx modality doms ->
  let i = Ctx.level ctx in
  (* To make these variables into values, we need to annotate them with their types, which in general are instantiations of the domains at previous variables.  Thus, we assemble them in a hashtable as we create them for random access to the previous ones. *)
  let argtbl = Hashtbl.create 10 in
  let j = ref 0 in
  let [ args; nfs ] =
    CubeOf.pmap
      {
        map =
          (fun fa [ dom ] ->
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find argtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let level = (i, !j) in
            j := !j + 1;
            let v = { tm = var modality level ty; ty = Lazy.from_val ty } in
            Hashtbl.add argtbl (SFace_of fa) v;
            [ v.tm; Ctx.Binding.make (Some level) v ]);
      }
      [ doms ] (Cons (Cons Nil)) in
  (args, nfs)

(* Extend a context by a finite number of cubes of new visible variables at some dimension, with boundaries, whose types are specified by the evaluation of some telescope in some (possibly higher-dimensional) environment (and hence may depend on the earlier ones).  Also return the new variables in a list of Cubes, and the new environment extended by the *top-dimensional variables only*. *)

type (_, _) modal_binding_cube =
  | Modal :
      ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim * ('k, 'dom Ctx.Binding.t) CubeOf.t
      -> ('n, 'mode) modal_binding_cube

(* Walk the already-evaluated iterated pi-type of a datatype constructor's function-type, introducing a cube of new variables for each of its domains, extending the context and environment.  This is used in match typechecking, where the constructor's function-type is stored (rather than a separate telescope of argument types).  In addition to the extended context and environment, the new variables (as values and as normals/bindings), and the VarAnnotate/bcomp data needed to relate the extended raw context to the branch body, we return the residual codomain "out" — the datatype applied to its parameters and this branch's indices — from which those indices can be read off.  The number of pattern variables (xs) is assumed to match the pi-depth (the caller checks this with Telescope.pi_arity), so a mismatch is an anomaly.

   The composition of the window modality with each domain's annotation, and the resulting variable creation and environment extension, exactly follow what would be done when walking the corresponding telescope entry. *)
type ('dom, 'window, 'mode, 'n, 'ac, 'e) ext_pi =
  | Ext_pi : {
      ctx : ('mode, 'ac, 'em) Ctx.t;
      env : ('dom, 'n, 'bc) env;
      values : ('n, 'dom, kinetic) modal_value_cube list;
      normals : ('n, 'mode) modal_binding_cube list;
      annotate : ('n, 'mode, 'annotations, 'mode, 'mode, 'm, 'mode) VarAnnotate.fwd_t;
      comp : ('mode, 'm, 'mode, 'e, unit, 'em) Tctx.bcomp;
      out : ('dom, kinetic) value;
    }
      -> ('dom, 'window, 'mode, 'n, 'ac, 'e) ext_pi

let rec ext_pi : type dom window mode a b c ac e n.
    (mode, a, e) Ctx.t ->
    (dom, window, mode) Modality.t ->
    (dom, n, b) env ->
    (a, c, ac) Raw.Namevec.t ->
    (dom, kinetic) value ->
    (dom, window, mode, n, ac, e) ext_pi =
 fun ctx window env xs ft ->
  match xs with
  (* The residual output type: the datatype applied to its parameters and this branch's indices.  It is uninstantiated (a "vertex" of the higher-dimensional type), which is exactly what indices_of_out expects. *)
  | [] ->
      Ext_pi
        {
          ctx;
          env;
          values = [];
          normals = [];
          annotate = Zero (Eq (Ctx.mode ctx));
          comp = Zero;
          out = ft;
        }
  | x :: xs -> (
      let m = dim_env env in
      (* The constructor's function-type is an uninstantiated m-dimensional pi-type; we view it as in check_at_pi (view_type would demand full instantiation). *)
      let (Viewed_pi { x = pix; filter = pifilter; doms; cods }) = view_constr_pi "ext_pi" m ft in
      (* The annotation is the (raw) modality of this pi's domain; we recompute its dimension filter and compose it with the window modality. *)
      let annotation = Modality.filter_modality pifilter in
      let (Has_filter afilter) = Modality.filter annotation m in
      let (Comp wx) = Modality.comp annotation in
      let modality = Modality.comp_out window wx in
      let (Has_filter filter_k_m) = Modality.filter modality m in
      match D.compare (Modality.filtered m afilter) (Modality.filtered m filter_k_m) with
      | Neq -> fatal (Unimplemented "filtering window modalities for higher-dimensional matches")
      | Eq -> (
          (* The pi's domain cube is already evaluated (at the annotation's filter); we introduce the variables for it directly, and obtain the codomain by applying the pi's top binder to them. *)
          match D.compare (Modality.filtered m afilter) (CubeOf.dim doms) with
          | Neq -> fatal (Anomaly "ext_pi domain dimension mismatch")
          | Eq ->
              let newvars, newnfs = dom_vars ctx modality doms in
              let x =
                match x with
                | Some x -> Some x
                | None -> option_of_binder_name (top_variable pix) in
              let filter_k_k = Modality.filter_idempotent filter_k_m in
              let (BindFam b) = BindCube.find_top cods in
              let output = apply_binder_term b pifilter newvars in
              let (Ext_pi { ctx; env; values = vars; normals = nfs; annotate; comp; out }) =
                ext_pi
                  (Ctx.cube_vis ctx filter_k_k x newnfs)
                  window
                  (Ext
                     {
                       env;
                       plus = D.plus_zero (Modality.filtered m afilter);
                       values = `Ok newvars;
                       filter = afilter;
                       filtered = Modality.filter_zero annotation;
                     })
                  xs output in
              Ext_pi
                {
                  ctx;
                  env;
                  values = Modal (afilter, newvars) :: vars;
                  normals = Modal (filter_k_m, newnfs) :: nfs;
                  annotate = Suc (Annotate filter_k_m, annotate);
                  comp = Suc (Dim (Modality.filtered m filter_k_m, filter_k_k), comp);
                  out;
                }))

(* Read the type indices of a match branch off the output type value produced by ext_pi (the datatype applied to its parameters and this branch's indices), checking that it is the expected datatype at the expected dimension with the expected number of indices.  The output is an uninstantiated ("vertex") datatype value, so we force its glued value rather than view_type it. *)
let indices_of_out : type dom m ij.
    (dom, kinetic) value -> m D.t -> ij Fwn.t -> ((m, dom normal) CubeOf.t, ij) Vec.t =
 fun out dim nindices ->
  match view_term out with
  | Neu { value; _ } -> (
      match force_eval value with
      | Val (Canonical { canonical = Data { dim = outdim; indices = Filled idx; _ }; _ }) -> (
          match (D.compare outdim dim, Fwn.compare (Vec.length idx) nindices) with
          | Eq, Eq -> idx
          | Neq, _ -> fatal (Anomaly "wrong dimension of output type in match branch")
          | _, Neq -> fatal (Anomaly "wrong number of indices in match branch"))
      | _ -> fatal (Anomaly "output type of constructor in match branch is not a datatype"))
  | _ -> fatal (Anomaly "output type of constructor in match branch is not neutral")

(* Extract a list of all the variables of a given kind in an iterated pi-type. *)
let rec get_pi_vars : type mode a b.
    (mode, a, b) Ctx.t ->
    [ `Cube | `Normal ] ->
    binder_name Bwd.t ->
    (mode, kinetic) value ->
    binder_name Bwd.t =
 fun ctx cube xs ty ->
  match View.view_type ty "get_pi_vars" with
  | Canonical (_, Pi { x; filter; doms; cods }, ins, tyargs) -> (
      let modality = Modality.filter_modality filter in
      let Eq = eq_of_ins_zero ins in
      match (D.compare_zero (CubeOf.dim doms), cube) with
      | Zero, `Normal | Pos _, `Cube ->
          let args, newnfs = dom_vars ctx modality doms in
          let (Any_ctx sctx) = Ctx.variables_vis ctx (Modality.filter_idempotent filter) x newnfs in
          (* If the variable is anonymous, fill in any display hints from its type. *)
          get_pi_vars sctx cube
            (Snoc (xs, top_variable (View.fill_hints doms x)))
            (tyof_app cods tyargs filter args)
      | _ -> xs)
  | _ -> xs

(* Given a datatype constructor (its parameter environment and its stored function-type), compute the variable-name display hints for each argument, by walking the constructor's evaluated function-type and extracting hints from the head canonical type of each domain.  Used by "split" to generate readable names for the pattern variables of a match.  The fresh variables created for each domain are only used to substitute into later domain types (via the pi's codomain) so as to find their heads, so we needn't track them carefully. *)
let constr_arg_hints : type mode m a e b.
    (mode, e, b) Ctx.t -> (mode, m, a) env -> (mode, a, kinetic) term -> hints Bwd.t =
 fun ctx env ty ->
  let rec go : (mode, kinetic) value -> hints Bwd.t -> hints Bwd.t =
   fun ft acc ->
    match view_term ft with
    | Neu { value; _ } -> (
        match force_eval value with
        | Val (Canonical { canonical = Pi { filter; doms; cods; _ }; _ }) ->
            let modality = Modality.filter_modality filter in
            let hints = View.hints_of_ty (CubeOf.find_top doms) in
            let newvars, _ = dom_vars ctx modality doms in
            let (BindFam b) = BindCube.find_top cods in
            go (apply_binder_term b filter newvars) (Snoc (acc, hints))
        | _ -> acc)
    | _ -> acc in
  go (Norm.eval_term env ty) Emp
