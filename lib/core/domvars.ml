open Bwd
open Util
open Modal
open Tbwd
open Dim
open Term
open Value
open Norm

(* To typecheck a lambda, do an eta-expanding equality check, check pi-types for equality, or read back a pi-type or a term at a pi-type, we must create one new variable for each argument in the boundary.  Sometimes we need these variables as values and other times as normals.  The function dom_vars creates these variables and returns them in two cubes.  It, and the function ext_tel below that follows from it, are in a separate file because it depends on Inst and Ctx and is used in Equal, Readback, and Check, and doesn't seem to be placed naturally in any of those files. *)

let dom_vars : type mode m a b.
    (mode, a, b) Ctx.t ->
    (m, (mode, kinetic) value) CubeOf.t ->
    (m, (mode, kinetic) value) CubeOf.t * (m, mode Ctx.Binding.t) CubeOf.t =
 fun ctx doms ->
  let i = Ctx.level ctx in
  let mode = Ctx.mode ctx in
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
            let v = { tm = var mode level ty; ty } in
            Hashtbl.add argtbl (SFace_of fa) v;
            [ v.tm; Ctx.Binding.make (Some level) v ]);
      }
      [ doms ] (Cons (Cons Nil)) in
  (args, nfs)

(* Extend a context by a finite number of cubes of new visible variables at some dimension, with boundaries, whose types are specified by the evaluation of some telescope in some (possibly higher-dimensional) environment (and hence may depend on the earlier ones).  Also return the new variables in a list of Cubes, and the new environment extended by the *top-dimensional variables only*. *)

module ModalBindingCube = Modality.Cube (struct
  type ('mode, 'a, 'b) t = 'mode Ctx.Binding.t
end)

let rec ext_tel : type mode a b c ac bc e ec n.
    (mode, a, e) Ctx.t ->
    (mode, n, b) env ->
    (* Note that c is a Fwn, since it is the length of a telescope. *)
    (a, c, ac) Raw.Namevec.t ->
    (mode, b, c, bc) Telescope.t ->
    (e, c, n, ec) Tbwd.snocs ->
    (mode, ac, ec) Ctx.t
    * (mode, n, bc) env
    * (n, mode, kinetic, unit) ModalValueCube.t list
    * (n, mode, unit, unit) ModalBindingCube.t list =
 fun ctx env xs tel ec ->
  match (xs, tel, ec) with
  | [], Emp, Zero -> (ctx, env, [], [])
  | x :: xs, Ext (x', modality, rty, rest), Suc ec ->
      let m = dim_env env in
      let lctx = Ctx.lock ctx modality in
      let lenv = key_env env (Modalcell.id modality) in
      let newvars, newnfs =
        dom_vars lctx
          (CubeOf.build m
             { build = (fun fa -> Norm.eval_term (act_env lenv (op_of_sface fa)) rty) }) in
      let x =
        match x with
        | Some x -> Some x
        | None -> x' in
      let ctx, env, vars, nfs =
        ext_tel
          (Ctx.cube_vis ctx modality x newnfs)
          (Ext (env, D.plus_zero m, modality, Ok newvars))
          xs rest ec in
      (ctx, env, Modal (modality, newvars) :: vars, Modal (modality, newnfs) :: nfs)

(* Extract a list of all the variables of a given kind in an iterated pi-type. *)
let rec get_pi_vars : type mode a b.
    (mode, a, b) Ctx.t ->
    [ `Cube | `Normal ] ->
    string option Bwd.t ->
    (mode, kinetic) value ->
    string option Bwd.t =
 fun ctx cube xs ty ->
  match View.view_type ty "get_pi_vars" with
  | Canonical (_, Pi (x, modality, doms, cods), ins, tyargs) -> (
      let Eq = eq_of_ins_zero ins in
      match (D.compare_zero (CubeOf.dim doms), cube) with
      | Zero, `Normal | Pos _, `Cube ->
          let lctx = Ctx.lock ctx modality in
          let args, newnfs = dom_vars lctx doms in
          let (Any_ctx sctx) = Ctx.variables_vis ctx modality x newnfs in
          get_pi_vars sctx cube (Snoc (xs, top_variable x)) (tyof_app cods tyargs modality args)
      | _ -> xs)
  | _ -> xs
