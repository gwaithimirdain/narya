open Bwd
open Modal
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

type ('mode, 'n, 'ac, 'bc, 'e) ext_tel =
  | Ext_tel : {
      ctx : ('mode, 'ac, 'em) Ctx.t;
      env : ('mode, 'n, 'bc) env;
      values : ('n, 'mode, kinetic) modal_value_cube list;
      normals : ('n, 'mode) modal_binding_cube list;
      annotate : ('n, 'mode, 'annotations, 'mode, 'mode, 'm, 'mode) VarAnnotate.fwd_t;
      comp : ('mode, 'm, 'mode, 'e, unit, 'em) Tctx.bcomp;
    }
      -> ('mode, 'n, 'ac, 'bc, 'e) ext_tel

let rec ext_tel : type mode a b c ac bc e n.
    (mode, a, e) Ctx.t ->
    (mode, n, b) env ->
    (* Note that c is a Fwn, since it is the length of a telescope. *)
    (a, c, ac) Raw.Namevec.t ->
    (mode, b, c, bc) Telescope.t ->
    (mode, n, ac, bc, e) ext_tel =
 fun ctx env xs tel ->
  match (xs, tel) with
  | [], Emp ->
      Ext_tel
        { ctx; env; values = []; normals = []; annotate = Zero (Eq (Ctx.mode ctx)); comp = Zero }
  | x :: xs, Ext (x', Modal (modality, plus, rty), rest) ->
      let m = dim_env env in
      let lenv = key_env env (Modalcell.id modality) plus in
      let (Has_filter filter_k_m) = Modality.filter modality m in
      let k = Modality.filtered m filter_k_m in
      let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter m filter_k_m)) in
      let newvars, newnfs =
        dom_vars ctx modality
          (CubeOf.build k
             { build = (fun fa -> Norm.eval_term (act_env flenv (opt_op_of_sface fa)) rty) }) in
      let x =
        match x with
        | Some x -> Some x
        | None -> x' in
      let filter_k_k = Modality.filter_idempotent filter_k_m in
      let (Ext_tel { ctx; env; values = vars; normals = nfs; annotate; comp }) =
        ext_tel
          (Ctx.cube_vis ctx filter_k_k x newnfs)
          (Ext
             {
               env;
               plus = D.plus_zero k;
               values = `Ok newvars;
               filter = filter_k_m;
               filtered = Modality.filter_zero modality;
             })
          xs rest in
      Ext_tel
        {
          ctx;
          env;
          values = Modal (filter_k_m, newvars) :: vars;
          normals = Modal (filter_k_m, newnfs) :: nfs;
          annotate = Suc (Annotate filter_k_m, annotate);
          comp = Suc (Dim (k, filter_k_k), comp);
        }

(* Extract a list of all the variables of a given kind in an iterated pi-type. *)
let rec get_pi_vars : type mode a b.
    (mode, a, b) Ctx.t ->
    [ `Cube | `Normal ] ->
    string option Bwd.t ->
    (mode, kinetic) value ->
    string option Bwd.t =
 fun ctx cube xs ty ->
  match View.view_type ty "get_pi_vars" with
  | Canonical (_, Pi { x; filter; doms; cods }, ins, tyargs) -> (
      let modality = Modality.filter_modality filter in
      let Eq = eq_of_ins_zero ins in
      match (D.compare_zero (CubeOf.dim doms), cube) with
      | Zero, `Normal | Pos _, `Cube ->
          let args, newnfs = dom_vars ctx modality doms in
          let (Any_ctx sctx) = Ctx.variables_vis ctx (Modality.filter_idempotent filter) x newnfs in
          get_pi_vars sctx cube (Snoc (xs, top_variable x)) (tyof_app cods tyargs filter args)
      | _ -> xs)
  | _ -> xs
