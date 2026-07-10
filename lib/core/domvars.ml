open Bwd
open Modal
open Reporter
open Dim
open Tctx
open Term
open Value
open Norm

(* To typecheck a lambda, do an eta-expanding equality check, check pi-types for equality, or read back a pi-type or a term at a pi-type, we must create one new variable for each argument in the boundary.  Sometimes we need these variables as values and other times as normals.  The function dom_vars creates these variables and returns them in two cubes.  It, and the function ext_tel below that follows from it, are in a separate file because it depends on Inst and Ctx and is used in Equal, Readback, and Check, and doesn't seem to be placed naturally in any of those files. *)

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
            let v = { tm = var modality level ty; ty } in
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

type ('dom, 'window, 'mode, 'n, 'ac, 'bc, 'e) ext_tel =
  | Ext_tel : {
      ctx : ('mode, 'ac, 'em) Ctx.t;
      env : ('dom, 'n, 'bc) env;
      values : ('n, 'dom, kinetic) modal_value_cube list;
      normals : ('n, 'mode) modal_binding_cube list;
      annotate : ('n, 'mode, 'annotations, 'mode, 'mode, 'm, 'mode) VarAnnotate.fwd_t;
      comp : ('mode, 'm, 'mode, 'e, unit, 'em) Tctx.bcomp;
    }
      -> ('dom, 'window, 'mode, 'n, 'ac, 'bc, 'e) ext_tel

let rec ext_tel : type dom window mode a b c ac bc e n.
    (mode, a, e) Ctx.t ->
    (dom, window, mode) Modality.t ->
    (dom, n, b) env ->
    (* Note that c is a Fwn, since it is the length of a telescope. *)
    (a, c, ac) Raw.Namevec.t ->
    (dom, b, c, bc) Telescope.t ->
    (dom, window, mode, n, ac, bc, e) ext_tel =
 fun ctx window env xs tel ->
  match (xs, tel) with
  | [], Emp ->
      Ext_tel
        { ctx; env; values = []; normals = []; annotate = Zero (Eq (Ctx.mode ctx)); comp = Zero }
  | x :: xs, Ext (x', Modal (annotation, plus, rty), rest) -> (
      let m = dim_env env in
      let lenv = key_env env (Modalcell.id annotation) plus in
      (* The dimension filter of the telescope annotation itself, at its (inner) codomain mode. *)
      let (Has_filter afilter) = Modality.filter annotation m in
      (* We compose the window modality with the telescope annotation to produce the eventual modality at the outer mode, and derive its dimension filter. *)
      let (Comp wx) = Modality.comp annotation in
      let modality = Modality.comp_out window wx in
      let (Has_filter filter_k_m) = Modality.filter modality m in
      (* A window modality must not further filter the annotation dimension. *)
      match D.compare (Modality.filtered m afilter) (Modality.filtered m filter_k_m) with
      | Neq -> fatal (Unimplemented "filtering window modalities for higher-dimensional matches")
      | Eq ->
          let k = Modality.filtered m filter_k_m in
          let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter m filter_k_m)) in
          let newvars, newnfs =
            dom_vars ctx modality
              (CubeOf.build k
                 { build = (fun fa -> Norm.eval_term (act_env flenv (opt_op_of_sface fa)) rty) })
          in
          let x =
            match x with
            | Some x -> Some x
            | None -> x' in
          let filter_k_k = Modality.filter_idempotent filter_k_m in
          let (Ext_tel { ctx; env; values = vars; normals = nfs; annotate; comp }) =
            ext_tel
              (Ctx.cube_vis ctx filter_k_k x newnfs)
              window
              (* The value environment lives at the annotation's (inner) mode, so it is extended by the annotation's filter, not the windowed one. *)
              (Ext
                 {
                   env;
                   plus = D.plus_zero k;
                   values = `Ok newvars;
                   filter = afilter;
                   filtered = Modality.filter_zero annotation;
                 })
              xs rest in
          Ext_tel
            {
              ctx;
              env;
              values = Modal (afilter, newvars) :: vars;
              normals = Modal (filter_k_m, newnfs) :: nfs;
              annotate = Suc (Annotate filter_k_m, annotate);
              comp = Suc (Dim (k, filter_k_k), comp);
            })

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

(* Given a datatype constructor (its parameter environment and the telescope of its argument types), compute the variable-name display hints for each argument, by evaluating each argument type and extracting hints from its head canonical type.  Used by "split" to generate readable names for the pattern variables of a match.  The fresh variables created to extend the environment are only used to substitute into later argument types so as to find their heads, so we needn't track them carefully. *)
let constr_arg_hints : type mode m a p ap e b.
    (mode, e, b) Ctx.t -> (mode, m, a) env -> (mode, a, p, ap) Telescope.t -> hints Bwd.t =
 fun ctx env args ->
  let rec go : type a p ap.
      (mode, m, a) env -> (mode, a, p, ap) Telescope.t -> hints Bwd.t -> hints Bwd.t =
   fun env tel acc ->
    match tel with
    | Emp -> acc
    | Ext (_, Modal (modality, plus_lock, rty), rest) ->
        let m = dim_env env in
        let lenv = key_env env (Modalcell.id modality) plus_lock in
        let (Has_filter filter) = Modality.filter modality m in
        let k = Modality.filtered m filter in
        let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter m filter)) in
        let doms =
          CubeOf.build k
            { build = (fun fa -> Norm.eval_term (act_env flenv (opt_op_of_sface fa)) rty) } in
        let newvars, _ = dom_vars ctx modality doms in
        let hints = View.hints_of_ty (CubeOf.find_top doms) in
        go
          (Ext
             {
               env;
               plus = D.plus_zero k;
               filter;
               filtered = Modality.filter_zero modality;
               values = `Ok newvars;
             })
          rest
          (Snoc (acc, hints)) in
  go env args Emp
