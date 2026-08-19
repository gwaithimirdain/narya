open Bwd
open Util
open Modal
open Tbwd
open Reporter
open Dim
open Tctx
open Term
open Value
open Domvars
open Act
open Norm
open Printable
module Binding = Ctx.Binding

(* The "Displaying" reader records whether we're reading back for printing to the user or for internal purposes.  For instance, when printing we do more eta-expansion if the user requested it.  Wrapping the "Displaying" module in another module called "Readback" and opening that module allows us to refer to the module as just "Displaying" here, but exports it as "Readback.Displaying" to other files even when they open this file. *)

module Readback = struct
  module Displaying = Algaeff.Reader.Make (Bool)
end

open Readback

let () =
  Displaying.register_printer (function `Read -> Some "unhandled Readback.Displaying.read effect")

(* Degenerating a context by a dimension (for the non-projectable instances of higher codata fields, when displaying a codatatype or comatch).  The degeneration itself is implemented in the downstream module Degctx, because it does an eval-readback cycle and hence depends on this file; but the readback/display code that consumes it lives here (below), so we make the degeneration a forward reference set by Degctx.  The result packages the degeneration plus-map, the degenerated context, and the canonical k-dimensional environment from it back to the original. *)
type (_, _, _, _) degctx =
  | Degctx :
      ('k, 'b, 'kb, 'mode) plusmap * ('mode, 'a, 'kb) Ctx.t * ('mode, 'k, 'b) env
      -> ('mode, 'a, 'b, 'k) degctx

type degctx_impl = {
  degctx : 'mode 'a 'b 'k. ('mode, 'a, 'b) Ctx.t -> 'k D.t -> ('mode, 'a, 'b, 'k) degctx;
}

let degctx_hook : degctx_impl ref =
  ref { degctx = (fun _ _ -> fatal (Anomaly "degctx not set (load Degctx)")) }

let set_degctx (impl : degctx_impl) = degctx_hook := impl

let degctx : type mode a b k. (mode, a, b) Ctx.t -> k D.t -> (mode, a, b, k) degctx =
 fun ctx k -> !degctx_hook.degctx ctx k

(* Similarly for bindsome. *)
type (_, _, _) bind_some =
  | Bind_some : {
      checked_perm : ('c, 'b) permute;
      oldctx : ('mode, 'a, 'c) Ctx.t;
      newctx : ('mode, 'a, 'c) Ctx.t;
    }
      -> ('mode, 'a, 'b) bind_some
  | Bind_none : ('mode, 'a, 'b) bind_some

type bind_some_impl = {
  bind_some :
    'mode 'b 'c 'd.
    'mode Mode.t * (level, 'mode normal) Hashtbl.t -> ('b, 'c, 'd) Ctx.t -> ('b, 'c, 'd) bind_some;
}

let bind_some_hook : bind_some_impl ref =
  ref { bind_some = (fun _ _ -> fatal (Anomaly "bind_some not set")) }

let set_bind_some (impl : bind_some_impl) = bind_some_hook := impl

let bind_some : type mode b c d.
    mode Mode.t * (level, mode normal) Hashtbl.t -> (b, c, d) Ctx.t -> (b, c, d) bind_some =
 fun v ctx -> !bind_some_hook.bind_some v ctx

(* Given a (viewed) type, compute whether its elements are type families, functions of another sort, or neither.  Right now, we do this by descending through Pi binders, extending the context. *)
let rec sort_of_ty : type mode a z.
    ?isfunc:bool -> (mode, z, a) Ctx.t -> mode View.view_type -> [ `Type | `Function | `Other ] =
 fun ?(isfunc = false) ctx -> function
  | Canonical (_, UU _, _, _) -> `Type
  | Canonical (_, Pi { x = _; filter; doms; cods }, _, tyargs) -> (
      match D.compare (TubeOf.inst tyargs) (BindCube.dim cods) with
      | Neq -> fatal (Dimension_mismatch ("sort_of_ty", TubeOf.inst tyargs, CubeOf.dim doms))
      | Eq ->
          let args, newnfs = dom_vars ctx (Modality.filter_modality filter) doms in
          let newctx = Ctx.invis ctx (Modality.filter_idempotent filter) newnfs in
          let output = tyof_app cods tyargs filter args in
          sort_of_ty ~isfunc:true newctx (view_type output "sort_of_ty"))
  | _ -> if isfunc then `Function else `Other

(* When a degeneracy acts on a variable or constant, the name it is displayed with (e.g. "refl", "Id", or "ap") depends on the sort of the *type of that variable or constant*, not on the type of the whole neutral application in which it occurs.  Since this only affects display, and computing it involves evaluating and descending through pi-types, we catch any errors and fall back on the generic name.  We can compute it in an empty context of the appropriate mode, since sort_of_ty uses the context only to create new variables. *)
let sort_of_val : type mode. mode Mode.t -> (mode, kinetic) value -> [ `Type | `Function | `Other ]
    =
 fun mode ty ->
  Reporter.try_with ~fatal:(fun _ -> `Other) @@ fun () ->
  sort_of_ty (Ctx.empty mode) (view_type ty "sort_of_val")

(* Whether a constant is defined to be a canonical type, possibly a family of them.  Such a constant is displayed with a superscript degeneracy rather than a name like "Id", even if the term in which it appears is not itself a type (e.g. a field projection out of a degenerated record type). *)
let rec is_canonical_def : type mode a. (mode, a, potential) term -> bool = function
  | Canonical _ -> true
  | Lam (_, _, _, body) -> is_canonical_def body
  | _ -> false

let is_canonical_const : Constant.t -> [ `Canonical | `Other ] =
 fun c ->
  Reporter.try_with ~fatal:(fun _ -> `Other) @@ fun () ->
  let (Definition { tm; _ }) = Global.find_const c in
  match tm with
  | `Defined tm when is_canonical_def tm -> `Canonical
  | _ -> `Other

(* The same question for a term rather than a value, by looking at the head of its application spine.  This is used when annotating a degeneracy at typechecking time, so that a term displayed without being read back (e.g. by the "synth" command) is displayed the same way as one that is read back. *)
let rec canonical_head : type mode a s. (mode, a, s) term -> [ `Canonical | `Other ] = function
  | Const c -> is_canonical_const c
  | App (_, fn, _, _, _) -> canonical_head fn
  | Inst (_, tm, _) -> canonical_head tm
  | Act (_, tm, _, _) -> canonical_head tm
  | Key { tm; _ } -> canonical_head tm
  | _ -> `Other

module ValuePair = struct
  type ('mode, 'a, 'b) t = ('mode, 'a) Value.value * ('mode, 'a) Value.value
end

module ModalValuePairCube = Modality.Cube (ValuePair)

(* An argument to readback that is present precisely when the energy is potential: the neutral whose potential value is being read back.  Reading back a comatch, or a canonical type, needs that neutral as the self-variable for computing its field or constructor types, and no other kind of value needs anything -- a potential value is a Lam, a Struct or a Canonical, never a Neu, so a neutral is never forced recursively and the display stays one-shot.  Like the status of type checking, it is rebuilt as readback descends through parameter abstractions. *)
type (_, _) readback_status =
  | Kinetic : ('mode, kinetic) readback_status
  | Potential : ('mode, kinetic) value -> ('mode, potential) readback_status

(* Descending through a parameter abstraction applies the self to the new variable, so that for instance "about Vec" reads its datatype back against "Vec A" rather than "Vec".  This is analogous to what check's status does when it extends its argument spine. *)
let apply_status : type mode s dom modality k n.
    (mode, s) readback_status ->
    (dom, modality, mode, k, n) Modality.filter_dim ->
    (k, (dom, kinetic) value) CubeOf.t ->
    (mode, s) readback_status =
 fun status filter args ->
  match status with
  | Kinetic -> Kinetic
  | Potential neutral -> Potential (apply_term neutral filter args)

(* Report, as information rather than an error, that some piece of a stuck case tree could not be displayed as the construct it came from, and return None so the caller shows its application spine.  These are all display-only shortfalls: the spine is always a correct thing to show, just a less informative one. *)
let no_display : type a. string -> a option =
 fun str ->
  emit (Case_tree_not_displayed str);
  None

(* Check whether a given normal is a free variable distinct from those already seen. *)
let is_fresh : type dom modality mode a b.
    (mode, a, b) Ctx.t ->
    (dom, modality, mode) Modality.t ->
    (level, unit) Hashtbl.t ->
    dom normal ->
    level =
 fun ctx window seen x ->
  (* With glued evaluation, an index can be a glued neutral whose stored value unfolds to a free variable, e.g. a transport along a variable that has been refined to reflexivity.  Such an index refines just as well as a bare variable, so we look through the unfolding.  (With glued evaluation off, view_term is the identity.) *)
  let (Locked (_, lctx)) = Ctx.lock ctx window in
  let err str =
    fatal (Matching_wont_refine ("index/boundary variable " ^ str, Some (PNormal (lctx, x)))) in
  match view_term x.tm with
  | Neu { head = Var { level; deg; key }; args = Emp; value; ty = _ } -> (
      match force_eval value with
      | Unrealized _ ->
          if Option.is_none (is_id_deg deg) then err "has degeneracy";
          (* Rebinding a variable rebinds what its *unkeyed* uses evaluate to, so a keyed use is not refined by binding its slot.  Unkeyed means an identity 2-cell on the variable's own annotation, which for a discriminee or an index is the match's window. *)
          (match Modalcell.compare key (Modalcell.id window) with
          | Eq -> ()
          | Neq -> err "is keyed");
          if Hashtbl.mem seen level then err "is a duplicate";
          Hashtbl.add seen level ();
          level
      | _ -> fatal (Anomaly "local variable bound to a potential term"))
  | _ -> err "is not free"

type (_, _, _, _) readback_apps =
  | Readback_apps :
      ('hmode, 'z, 'c) Ctx.t * (('hmode, 'c, 's) term -> ('mode, 'a, 's) term)
      -> ('hmode, 'mode, 'a, 's) readback_apps

(* Readback of values to terms.  Closely follows equality-testing in equal.ml, so most comments are omitted.  However, unlike equality-testing and the "readback" in theoretical NbE, this readback does *not* eta-expand functions and tuples.  It is used for (1) displaying terms to the user, who will usually prefer not to see things eta-expanded, and (2) turning values into terms so that we can re-evaluate them in a new environment, for which purpose eta-expansion is irrelevant.  There are two exceptions:

   1. When reading back at a record type that the user has marked as transparent, we eta-expand tuples.  This is chosen based on the readback type.
   2. When reading back a higher-dimensional pi-type, we eta-expand its instantiation arguments so that we can display it prettily.  This is controlled by the flag ~eta.

   In typechecking we only ever read back kinetic terms.  But reading back potential terms is useful for displaying definitions to the user, so we work as energy-polymorphically as possible.  At present we allow ourselves to fail sometimes on potential terms, in which case display falls back to just showing a stuck spine; but readback on a kinetic term should never fail. *)

(* ********** Primary readback functions ********** *)

(* These functions deal primarily with kinetic values, and with the value types that are shared between kinetic and potential values, but they include hooks to detect when readback of potential values is called for and pass off to those functions defined later. *)

(* To read back a normal form, we simply dispatch to type-directed readback at its stored type.  *)
let rec readback_nf : type mode a z.
    ?eta:bool -> (mode, z, a) Ctx.t -> mode normal -> (mode, a, kinetic) term =
 fun ?(eta = false) n x -> readback_at ~eta Kinetic n x.tm (Lazy.force x.ty)

(* Read back an evaluation at a specified type.  Recall that a kinetic evaluation is always a Val, so in that case we are just passing off to readback_at.  In the potential case, this is how we read back the result of *applying* a potential value (a case-tree lambda). *)
and readback_eval : type mode a z s.
    ?eta:bool ->
    (mode, s) readback_status ->
    (mode, z, a) Ctx.t ->
    (mode, s) evaluation ->
    (mode, kinetic) value ->
    (mode, a, s) term =
 fun ?(eta = false) status ctx ev ty ->
  match (ev, status) with
  | Val v, _ -> readback_at ~eta status ctx v ty
  (* In the realize case the value is kinetic, so the stored self-term in the Potential status is discarded. *)
  | Realize v, _ -> Realize (readback_at ~eta Kinetic ctx v ty)
  (* A genuinely stuck case tree may record the match it got stuck on, in which case we display that match.  If it doesn't, or if we can't reconstruct it, we fall back on the neutral that the status carries -- only a potential readback can meet an Unrealized, so that neutral is always available -- and show its application spine for this component. *)
  | Unrealized (Some pn), Potential neutral -> (
      match readback_stuck status ctx pn ty with
      | Some tm -> tm
      | None -> Realize (readback_val ctx neutral))
  | Unrealized None, Potential neutral -> Realize (readback_val ctx neutral)

(* Readback is energy-polymorphic: it reads back a value of any energy 's into an ('a, 's) term.  In practice it is only ever called on a *potential* value for display (reading back the forced value of a neutral); in particular, that's the only way a comatch (a no-eta struct) reaches the readback-at-Codata branch.  All other callers read back only kinetic values, with neutral resulting in application spines. *)
and readback_at : type mode a z s.
    ?eta:bool ->
    (mode, s) readback_status ->
    (mode, z, a) Ctx.t ->
    (mode, s) value ->
    (mode, kinetic) value ->
    (mode, a, s) term =
 fun ?(eta = false) status ctx tm ty ->
  let view = if Displaying.read () then view_term tm else tm in
  let vty = view_type ty "readback_at" in
  match (vty, view) with
  (* Abstractions (kinetic or potential) are read back uniformly by extending the context using their pi-type. *)
  | Canonical (_, Pi { x = _; filter; doms; cods }, ins, tyargs), Lam (x, filter2, body) -> (
      let Eq = eq_of_ins_zero ins in
      (* The instantiation of the type, and the dimension of the binder, are both the *outer* (unfiltered) dimension of the pi-type; the variable cube and the domains live at the filtered dimension. *)
      let n = BindCube.dim cods in
      let l = dim_binder body in
      let modality = Modality.filter_modality filter in
      match
        ( D.compare (TubeOf.inst tyargs) n,
          D.compare n l,
          Modality.compare modality (Modality.filter_modality filter2) )
      with
      | Neq, _, _ -> fatal (Dimension_mismatch ("reading back at pi 1", TubeOf.inst tyargs, n))
      | _, Neq, _ -> fatal (Dimension_mismatch ("reading back at pi 2", n, l))
      | _, _, Neq ->
          fatal
            (Modality_mismatch
               (`Internal, "reading back at pi 3", modality, Modality.filter_modality filter2))
      | Eq, Eq, Eq ->
          let Eq = Modality.filter_uniq filter filter2 in
          let (Variables (m, mn, xs) as x) = View.fill_hints doms x in
          let args, newnfs = dom_vars ctx modality doms in
          let (Plus af) = N.plus (NICubeOf.out N.zero xs) in
          let newctx = Ctx.vis ctx (Modality.filter_idempotent filter) m mn xs newnfs af in
          let output = tyof_app cods tyargs filter args in
          let body =
            readback_eval ~eta (apply_status status filter args) newctx (apply tm filter args)
              output in
          Term.Lam (x, n, filter, body))
  (* If eta-expansion of functions is enabled, we do an eta-expanding readback of any term at a pi-type. *)
  | Canonical (_, Pi { x = name; filter; doms; cods }, ins, tyargs), tm when eta ->
      let modality = Modality.filter_modality filter in
      let Eq = eq_of_ins_zero ins in
      let name = View.fill_hints doms name in
      let newargs, newnfs = dom_vars ctx modality doms in
      let (Any_ctx newctx) = Ctx.variables_vis ctx (Modality.filter_idempotent filter) name newnfs in
      let output = tyof_app cods tyargs filter newargs in
      (* We carry through the eta-expansion flag so that iterated pi-types will eta-expand fully. *)
      Term.Lam
        ( name,
          BindCube.dim cods,
          filter,
          readback_eval ~eta
            (apply_status status filter newargs)
            newctx (apply tm filter newargs) output )
  (* At a record type, eta-expansion is controlled by the type's eta and opacity rather than the eta argument passed to readback_at.  We also read back explicit structs (tuples and comatches) here even at non-eta-expanding codatatypes. *)
  | ( Canonical
        (type hmode mn m n)
        (( _,
           Codata
             (type a et)
             ({ eta; opacity; fields = codata_fields; _ } as codata_args :
               (mode, m, n, a, et) codata_args),
           ins,
           _ ) :
          (hmode, kinetic) head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      _ ) -> (
      (* The term 'view' has the polymorphic energy 's'.  We also need a uniformly kinetic version of this term; if the energy is kinetic this is the same term, otherwise it is the stored neutral in the potential status. *)
      match
        match (eta, status) with
        | _, Potential neutral -> Some (neutral, (Potential : s energy), (eta : (s, et) eta))
        | Eta, Kinetic -> Some (view, Kinetic, Eta)
        | Noeta, Kinetic -> None
      with
      (* A readback of a kinetic term (necessarily a neutral) at a no-eta codatatype just yields its application spine. *)
      | None -> readback_val ctx tm
      (* In other cases, we might read back a struct. *)
      | Some (ktm, energy, eta) -> (
          let dim = cod_left_ins ins in
          let fldins = ins_zero dim in
          let evaldim = dim_env codata_args.env in
          (* A nontrivially permuted record is not a record type, but we can permute its arguments to find elements of a record type that we can then eta-expand and re-permute. *)
          let ktm, tm, ty, wrap =
            match is_id_ins ins with
            | Some _ -> (ktm, view, ty, fun res -> res)
            | None ->
                let (Perm_to p) = perm_of_ins ins in
                let pinv = deg_of_perm (perm_inv p) in
                let ptm = act_value view pinv (Modalcell.id2 (Ctx.mode ctx)) in
                let pty = act_ty ktm ty pinv (Modalcell.id2 (Ctx.mode ctx)) in
                let pktm : (mode, kinetic) value =
                  match energy with
                  | Kinetic -> ptm
                  | Potential -> act_value ktm pinv (Modalcell.id2 (Ctx.mode ctx)) in
                (pktm, ptm, pty, fun res -> Term.Act (energy, res, deg_of_perm p, (`Other, `Other)))
          in
          let m = cod_left_ins ins in
          let codata_fields =
            Bwd.filter
              (fun (CodatafieldAbwd.Entry
                      (type i)
                      ((_, Codatafield (_, Adjunction { left; _ }, _, _)) :
                        i Field.t * (i, mode * a * D.zero * n * _) Codatafield.t)) ->
                let (Has_filter left_filter) = Modality.filter left m in
                Option.is_some (Modality.filter_is_trivial m left_filter))
              codata_fields in
          match tm with
          (* If the term is a struct, we read back its fields.  Even though this is not technically an eta-expansion, we have to do it here rather than in readback_val because we need the codata type to determine the types at which to read back the fields. *)
          | Struct { fields = comatch_fields; energy; ins = value_ins; eta = _ } -> (
              match D.compare (cod_left_ins value_ins) dim with
              | Neq -> fatal (Anomaly "comatch readback: struct dimension does not match its type")
              | Eq ->
                  let readback_field (Value.StructfieldAbwd.Entry (fld, sf)) :
                      (mode * (_ * _ * s * et)) Term.StructfieldAbwd.entry =
                    match Term.CodatafieldAbwd.find_opt codata_fields fld with
                    (* Lower field *)
                    | Found
                        (Codatafield (_, (Adjunction { left; right; unit; _ } as adj), _, Lower _))
                      ->
                        (* We project the field from the neutral-as-self, keying by the adjunction unit and reading back the component behind the right-adjoint lock. *)
                        let xu = act_value ktm (id_deg D.zero) unit in
                        let tyu = act_ty ktm ty (id_deg D.zero) unit in
                        let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                        (* Build a status and an acted term at energy 's' for energy-polymorphic readback of the body. *)
                        let ((status, sxu) : (_, s) readback_status * (mode, s) value) =
                          match status with
                          | Kinetic -> (Kinetic, xu)
                          | Potential neutral ->
                              let (Val fneu) = field left neutral fld fldins in
                              (Potential fneu, act_value tm (id_deg D.zero) unit) in
                        (* Read back the body term *)
                        let rtm =
                          readback_eval status lctx
                            (field left sxu fld (ins_zero dim))
                            (tyof_field left (Ok xu) tyu fld (ins_zero evaldim)) in
                        let l =
                          match sf with
                          | Lower (_, _, l) -> l
                          | _ -> `Labeled in
                        Entry (fld, Lower (adj, plus_lock, rtm, l))
                    (* Higher field *)
                    | Found
                        (Codatafield (_, (Adjunction { left; right; unit; _ } as adj), _, Higher _))
                      -> (
                        match Value.StructfieldAbwd.find_opt comatch_fields fld with
                        | Found (Higher (lazy hd)) ->
                            (match Modalcell.compare_adjunction hd.adj adj with
                            | Neq -> fatal (Anomaly "comatch readback: field adjunction mismatch")
                            | Eq -> ());
                            let (Locked (ctx_plus_lock, _)) = Ctx.lock ctx right in
                            (* The self, keyed by the adjunction unit, and its type, exactly as for a lower field. *)
                            let selfnf =
                              {
                                tm = act_value ktm (id_deg D.zero) unit;
                                ty = lazy (act_ty ktm ty (id_deg D.zero) unit);
                              } in
                            let pbm =
                              Term.PlusPbijmap.build dim (Field.dim fld)
                                {
                                  build =
                                    (fun pbij ->
                                      let (Pbij (fldins, fldshuf)) = pbij in
                                      let r = left_shuffle fldshuf in
                                      (* The instance's body lives in the context degenerated by its remaining dimensions, so we build it there, as check_higher_field does: degenerate the context, commute the degeneracy past the right-adjoint lock, and lock the degenerated context to it. *)
                                      let (Degctx (plusmap, dctx, denv)) = degctx ctx r in
                                      let (Shift (plusmap_bg, deg_plus_lock)) =
                                        shift_unplus_lock r plusmap ctx_plus_lock in
                                      let dlctx = Ctx.lock_to dctx right deg_plus_lock in
                                      (* Raise the self into that context, where the remaining dimensions are genuine dimensions and this instance is therefore *projectable*: ins_plus_of_pbij absorbs them into the evaluation dimension, turning the partial bijection into an insertion.  This is the move check_higher_field makes to carry its status into a component.  The body is then just a field projection read back like a lower field's -- the comatch's closure environment never has to be transported, and no shuffleable is needed, since at this dimension nothing remains. *)
                                      let dself = degenerate_normal ctx denv r selfnf in
                                      (* Degenerating the self reads it back and re-evaluates it, so it survives that round trip only if its spine really does evaluate to the comatch.  An ordinary self does; the one readback_stuck_match supplies in a match branch does not, when it could not refine the discriminee -- there the spine is still a stuck match, so projecting from it computes nothing and we would show an instance body that is not the one the comatch stores.  We detect that and abandon back to the match. *)
                                      (match dself.tm with
                                      | Neu { value; _ } -> (
                                          match force_eval value with
                                          | Val (Struct _) -> ()
                                          | _ -> fatal Degenerated_neutral_not_a_struct)
                                      | _ -> fatal Degenerated_neutral_not_a_struct);
                                      let (Plus rm) = D.plus dim in
                                      let newins = ins_plus_of_pbij fldins fldshuf rm in
                                      let ety =
                                        tyof_field left (Ok dself.tm) (Lazy.force dself.ty) fld
                                          newins in
                                      let rtm =
                                        readback_at Kinetic dlctx
                                          (field_term left dself.tm fld newins)
                                          ety in
                                      Some (PlusFam.PlusFam (plusmap_bg, Realize rtm)));
                                } in
                            Entry (fld, Higher (adj, ctx_plus_lock, pbm))
                        | _ -> fatal (Anomaly "comatch readback: higher field missing from comatch")
                        )
                    | _ -> fatal (Anomaly "comatch readback: field not found in codata type") in
                  let fields = Bwd.map readback_field comatch_fields in
                  wrap (Term.Struct { eta; dim; fields; energy }))
          (* In addition, if a record type is transparent, or if it's translucent and the term is a tuple in a case tree, and we are reading back for display (rather than for internal typechecking purposes), we do an eta-expanding readback. *)
          | _ -> (
              match eta with
              | Eta -> (
                  match opacity with
                  | (`Transparent l | `Translucent l)
                    when Displaying.read ()
                         &&
                         match (tm, opacity) with
                         | Neu { value; _ }, `Translucent _ -> (
                             match force_eval value with
                             | Val (Struct _) -> true
                             | _ -> false)
                         | _, `Transparent _ -> true
                         | _ -> false ->
                      (* A modal field whose (left adjoint) modality is nonparametric disappears at a dimension it filters nontrivially, so it isn't read back. *)
                      let fields =
                        Mbwd.map
                          (fun (CodatafieldAbwd.Entry
                                  (type i)
                                  (( fld,
                                     Codatafield
                                       (type f g gmode ag)
                                       ((_, (Adjunction { left; right; unit; _ } as adj), _, Lower _) :
                                         _
                                         * (mode, f, g, gmode) Modalcell.adjunction
                                         * (_, mode, g, gmode, ag) plus_lock
                                         * _) ) :
                                    i Field.t * (i, mode * a * D.zero * n * has_eta) Codatafield.t))
                             ->
                            (* Eta-expansion of a modal field: key the term by the adjunction unit, project, and read back the component in the context locked by the right adjoint (as in the eta-rule for equality). *)
                            let xu = act_value ktm (id_deg D.zero) unit in
                            let tyu = act_ty ktm ty (id_deg D.zero) unit in
                            let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                            (* Build a status and an acted term at energy 's' for energy-polymorphic readback of the body. *)
                            let ((status, sxu) : (gmode, s) readback_status * (mode, s) value) =
                              match status with
                              | Kinetic -> (Kinetic, xu)
                              | Potential neutral ->
                                  let (Val fneu) = field left neutral fld fldins in
                                  (Potential fneu, act_value tm (id_deg D.zero) unit) in
                            let rtm =
                              readback_eval status lctx (field left sxu fld fldins)
                                (tyof_field left (Ok xu) tyu fld fldins) in
                            Term.StructfieldAbwd.Entry
                              (fld, Term.Structfield.Lower (adj, plus_lock, rtm, l)))
                          codata_fields in
                      wrap (Struct { eta = Eta; dim; fields; energy })
                  (* If the term is not a struct and the record type is not transparent/translucent, we pass off to synthesizing readback. *)
                  | _ -> readback_val ctx view)
              | _ -> readback_val ctx view)))
  (* Datatypes are not eta-expanding, but we still need the datatype in order to read back a constructor at that type. *)
  | Canonical (_, Data { constrs; _ }, ins, tyargs), Constr (xconstr, xn, xargs) -> (
      let Eq = eq_of_ins_zero ins in
      (* Pick out the constructor of the datatype that matches the one we're reading back *)
      let (Dataconstr { env; ty }) =
        Abwd.find_opt xconstr constrs <|> Anomaly "constr not found in readback" in
      match D.compare xn (TubeOf.inst tyargs) with
      | Neq -> fatal (Dimension_mismatch ("reading back constrs", xn, TubeOf.inst tyargs))
      | Eq ->
          let (Wrap xargs) = Vec.of_list xargs in
          let lgth = Vec.length xargs in
          (* If a higher-dimensional constructor belongs to a higher version of a datatype, the instantiation arguments of the latter must be lower-dimensional versions of the same constructor.  We extract their arguments to form the boundaries of the types of the arguments of our current constructor. Specifically, tyargs is a tube of normals, each of which is expected to be a lower-dimensional instance of the same constructor, which therefore has a list of modal cubes as arguments.  We want to extract the top element of each of those cubes to form a *list of tubes* of modal values, whereas what we naturally have, after peeling off the constructors, is a *tube of lists*.  We do the conversion with our multiple-output traversal with a variable number of outputs, specifically the length of the telescope. *)
          let tyarg_args =
            find_tyarg_args ~check_dim:"reading back constrs" xconstr lgth tyargs
              ~wrong_arity:(fun () ->
                Readback_at_wrong_type
                  "a constructor whose instantiation argument has the wrong number of arguments")
              ~wrong_constr:(fun _ ->
                Readback_at_wrong_type
                  "a constructor whose instantiation argument is a different constructor")
              ~not_constr:(fun _ ->
                Readback_at_wrong_type
                  "a constructor whose instantiation argument is not a constructor") in
          (* Now xargs and tyarg_args are guaranteed to have the same length, so readback_at_pi doesn't have to worry. *)
          Constr
            ( xconstr,
              dim_env env,
              readback_at_pi ctx (dim_env env) (lazy (eval_term env ty)) xargs tyarg_args ))
  (* Reading back canonical types themselves (data, codata, record), *at* a universe, happens only for potential terms. *)
  | ( Canonical
        (type hmode m n mn)
        ((_, UU (_, mk), ins0, boundary) :
          (hmode, kinetic) head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      Canonical { canonical; ins; tyargs; _ } ) -> (
      let (Potential neutral) = status in
      (* The universe has intrinsic dimension zero, so its substitution dimension equals its total dimension mk. *)
      let Eq = eq_of_ins_zero ins0 in
      (* The uninstantiated part of the value's dimension is the dimension of the universe it belongs to. *)
      match D.compare (TubeOf.uninst tyargs) mk with
      | Neq -> fatal (Anomaly "uninst dim of canonical is not that of its universe")
      | Eq -> (
          match canonical with
          | Data data_args ->
              (* Datatypes never have a Gel dimension, so the insertion is always trivial. *)
              let Eq = eq_of_ins_zero ins in
              Inst
                ( Potential,
                  readback_data ctx data_args,
                  TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ tyargs ] )
          (* Codatatypes and records are handled uniformly whether 0-dimensional, intrinsically higher (Gel-like), or degenerate, instantiated or not, and whether or not their fields are modal.  Unlike a datatype, an instantiated one is *not* read back uninstantiated and re-instantiated: the boundary of a degenerate codatatype behaves like parameters rather than like indices, so it is the instantiated form that behaves like a codatatype, and it is displayed as one.  Hence the instantiation arguments are passed along rather than read back separately here.
             The insertion splits the value's total dimension into its evaluation dimension and its intrinsic (Gel) dimension, which are the two dimensions the displayed codatatype records.  When the insertion is the identity, the two are in that order and the value is displayed directly; otherwise the value is not a record type at all (its fields can't even be projected), but it is a permutation of one, so we un-permute it, display that, and wrap the result in the permutation as a degeneracy action. *)
          | Codata codata_args -> (
              match is_id_ins ins with
              | Some cm_cn -> readback_codata ctx neutral tyargs codata_args boundary cm_cn
              | None -> readback_permuted_codata ctx neutral tyargs ins)
          | UU _ | Pi _ -> Realize (readback_val ctx neutral)))
  | _ -> readback_val ctx tm

(* The synthesizing readback only ever applies to neutrals (a kinetic value).  Any other value reaching it (which can only be a potential value, since other callers pass kinetic neutrals) is an anomaly. *)
and readback_val : type mode a z s. (mode, z, a) Ctx.t -> (mode, s) value -> (mode, a, s) term =
 fun ctx x ->
  match x with
  | Neu { head; args; value; ty } -> (
      match (force_eval value, Displaying.read ()) with
      | Realize v, true -> readback_at Kinetic ctx v (Lazy.force ty)
      | Val (Canonical _), _ -> readback_neu ~canonical:`Canonical ctx head args
      | _ -> readback_neu ~canonical:`Other ctx head args)
  | Lam _ -> fatal (Readback_at_wrong_type "a lambda, which does not synthesize")
  | Struct _ -> fatal (Readback_at_wrong_type "a struct, which does not synthesize")
  | Constr _ -> fatal (Readback_at_wrong_type "a constructor, which does not synthesize")
  | Canonical _ -> fatal (Readback_at_wrong_type "a canonical type, which does not synthesize")

(* Read back an application spine, yielding the context its head must be displayed in (the outer context locked by the left adjoint of every field projection the spine crosses) together with the function that puts the spine back around a term displayed there. *)
and readback_apps : type hmode mode a z any s.
    s energy ->
    ?pi:bool ->
    (mode, z, a) Ctx.t ->
    (hmode, mode, any) apps ->
    (hmode, mode, a, s) readback_apps =
 fun energy ?(pi = false) ctx -> function
  | Emp -> Readback_apps (ctx, fun tm -> tm)
  | Arg (rest, filter, args, ins) ->
      let modality = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      let (Locked (plus, lctx)) = Ctx.lock ctx modality in
      let (Readback_apps (hctx, rewrap)) = readback_apps energy ~pi ctx rest in
      Readback_apps
        ( hctx,
          fun tm ->
            Term.Act
              ( energy,
                App
                  ( energy,
                    rewrap tm,
                    cod_left_ins ins,
                    filter,
                    Modal
                      ( modality,
                        plus,
                        CubeOf.mmap { map = (fun _ [ x ] -> readback_nf lctx x) } [ args ] ) ),
                p,
                (`Other, `Other) ) )
  | Inst (rest, _, args) ->
      let (Readback_apps (hctx, rewrap)) = readback_apps energy ~pi ctx rest in
      (* When reading back a fully instantiated higher-dimensional pi-type, we eta-expand the instantiation arguments so that it can be printed with a nice notation. *)
      let eta = pi && TubeOf.is_full args in
      Readback_apps
        ( hctx,
          fun tm ->
            Inst
              ( energy,
                rewrap tm,
                TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ~eta ctx x) } [ args ] ) )
  (* A field projection crosses to the mode the field's left adjoint comes from, so the rest of the spine, and the match at its end, live in our context locked by it. *)
  | Field (rest, filter, fld, fldplus, ins) -> (
      let fm = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx fm in
      let t = cod_left_ins ins in
      let (Readback_apps (hctx, rewrap)) = readback_apps energy ~pi lctx rest in
      match Modality.filter_is_trivial t filter with
      | Some Eq ->
          (* Trivial filter: the inner spine is at the full result dimension t, and we build the projection there directly. *)
          Readback_apps
            ( hctx,
              fun tm ->
                Term.Act
                  ( energy,
                    Field (energy, Modal (fm, plus_lock, rewrap tm), fld, id_ins t fldplus),
                    p,
                    (`Other, `Other) ) )
      | None ->
          (* Nontrivial filter: the field's modality is nonparametric and a degeneracy has acted, so the inner spine lives at a strictly smaller filtered dimension ft than the result dimension t.  We read back the projection at ft and lift it to t by the filter's degeneracy, which reconstructs (and prints as) the acting degeneracy.  This is exactly the "disappeared" projection viewed as a degeneracy of a lower-dimensional one, and it re-evaluates correctly since eval filters the environment dimension. *)
          let ft = Modality.filtered t filter in
          let (Plus new_fldplus) = D.plus (D.plus_right fldplus) in
          let liftdeg = Modality.deg_of_filter t filter in
          Readback_apps
            ( hctx,
              fun tm ->
                Term.Act
                  ( energy,
                    Term.Act
                      ( energy,
                        Field (energy, Modal (fm, plus_lock, rewrap tm), fld, id_ins ft new_fldplus),
                        liftdeg,
                        (`Other, `Other) ),
                    p,
                    (`Other, `Other) ) ))

and readback_neu : type hmode mode a z any.
    ?canonical:[ `Canonical | `Other ] ->
    (mode, z, a) Ctx.t ->
    (hmode, kinetic) head ->
    (hmode, mode, any) apps ->
    (mode, a, kinetic) term =
 fun ?(canonical = `Other) ctx head apps ->
  let pi =
    match head with
    | Pi _ -> true
    | _ -> false in
  let (Readback_apps (hctx, rewrap)) = readback_apps Kinetic ~pi ctx apps in
  (* The degeneracies appearing on the spine of a neutral are all *permutations*, which are never displayed with a name like "refl" or "Id" that depends on the sort of their argument.  Thus the only place the sort matters is at the head, where it is computed from the type of the head itself (see readback_head).  Here we only pass along whether the whole neutral is a canonical type, which determines whether a reflexivity at the head is displayed as a superscript. *)
  rewrap (readback_head ~canonical hctx head)

and readback_head : type mode c z.
    ?canonical:[ `Canonical | `Other ] ->
    (mode, z, c) Ctx.t ->
    (mode, kinetic) head ->
    (mode, c, kinetic) term =
 fun ?(canonical = `Other) ctx h ->
  match h with
  | Var { level; deg; key } -> (
      (* The source of the key is supposed to be the modal annotation of the variable, while its target is supposed to be the composite of all the locks in the context to its right (including any added by the degeneracy).  So we remove its target from the context. *)
      let (Remove_lock (ctx, plus_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt key) in
      (* Now we look for the level variable in the remaining context. *)
      let (Lookup
             { result; value; dirt = _; modality; filter; insert; plus = Plus_with_locks (c, _) }) =
        Ctx.find_level ctx level <|> No_such_level (PLevel level) in
      (* We check that (1) the modality annotating that variable is the source of the key, and (2) there are no more locks remaining to its right in the context. *)
      match (Modality.compare (Modalcell.vsrc key) modality, result, c) with
      | Eq, `Var (_, fa), Zero -> (
          (* We put the source/annotation modality back onto the context as a lock, as the "Var" term expects. *)
          let (Has_plus_lock plus_src) = plus_lock modality in
          (* If there's a nontrivial degeneracy, we act by it; otherwise we leave it off. *)
          let iplus = plus_with_locks_of_plus_lock plus_src in
          let tm =
            match is_id_deg deg with
            | Some _ -> Term.Var (Index (insert, fa, filter, iplus))
            | None ->
                (* The degeneracy acts on the variable itself, so its display name is determined by the sort of the variable's own type. *)
                let sort = sort_of_val (Modality.src modality) (Lazy.force value.ty) in
                Act (Kinetic, Term.Var (Index (insert, fa, filter, iplus)), deg, (sort, canonical))
          in
          (* And if the key is nontrivial, we act by it; otherwise we leave it off. *)
          match (Modality.compare_id modality, plus_src, plus_tgt) with
          | Eq, Plus_lock (Zero _, Zero), Plus_with_locks (Zero, Zero _) -> tm
          | _ -> Key { tm; cell = key; plus_tgt; plus_src })
      | Neq, _, _ ->
          fatal (Modality_mismatch (`Internal, "reading back var", Modalcell.vsrc key, modality))
      | _, _, Suc _ -> fatal (Anomaly "reading back var: key has insufficient codomain")
      | _, `Field _, _ -> .)
  | Const { name; ins } -> (
      let dim = cod_left_ins ins in
      let (To perm) = deg_of_ins ins in
      let (DegExt (_, _, deg)) = comp_deg_extending (deg_zero dim) perm in
      match is_id_deg deg with
      | Some _ -> Const name
      | None ->
          (* Likewise, a degeneracy acting on a constant is displayed according to the sort of the constant's own type, and according to whether that constant is (a family of) canonical types. *)
          let sort =
            Reporter.try_with ~fatal:(fun _ -> `Other) @@ fun () ->
            let (Definition { mode; ty; _ }) = Global.find_const name in
            sort_of_val mode (eval_term (Emp (mode, D.zero)) ty) in
          let canonical =
            match is_canonical_const name with
            | `Canonical -> `Canonical
            | `Other -> canonical in
          Act (Kinetic, Const name, deg, (sort, canonical)))
  | Meta { meta; env; ins } -> (
      let tm = MetaEnv (meta, readback_env ctx env (Global.find_meta meta).termctx) in
      match is_id_ins ins with
      | Some _ -> tm
      | None ->
          (* A degeneracy on a metavariable is always a permutation, whose display doesn't depend on the sort. *)
          let (To perm) = deg_of_ins ins in
          Act (Kinetic, tm, perm, (`Other, canonical)))
  | UU (mode, n) -> UU (mode, n)
  | Pi args -> readback_pi ctx args

and readback_pi : type c z dom modality mode k n.
    (mode, z, c) Ctx.t -> (dom, modality, mode, k, n) pi_args -> (mode, c, kinetic) term =
 fun ctx { x; filter; doms; cods } ->
  let n = BindCube.dim cods in
  let modality = Modality.filter_modality filter in
  let x = View.fill_hints doms x in
  let (Locked (plus, lctx)) = Ctx.lock ctx modality in
  let args, newnfs = dom_vars ctx modality doms in
  let build : type l. (l, n) sface -> (l, dom * modality * mode * c) CodFam.t =
   fun fa ->
    let (Filter_sface (fb, kfilter)) = Modality.filter_sface filter fa in
    let (Any_ctx sctx) =
      Ctx.variables_vis ctx
        (Modality.filter_idempotent kfilter)
        (sub_variables fb x) (CubeOf.subcube fb newnfs) in
    let sargs = CubeOf.subcube fb args in
    let (BindFam b) = BindCube.find cods fa in
    Cod (kfilter, readback_val sctx (apply_binder_term b kfilter sargs)) in
  Term.Pi
    {
      x;
      filter;
      doms =
        Modal
          (modality, plus, CubeOf.mmap { map = (fun _ [ dom ] -> readback_val lctx dom) } [ doms ]);
      cods = CodCube.build n { build };
    }

(* Read back a vector of values, whose types are the domains of the constructor's function-type.  That function-type is walked one argument at a time, applying its codomain to each argument as it is read back.  Each domain also has to be instantiated at a boundary, supplied as a vector of tubes. *)
and readback_at_pi : type mode n c b z.
    (mode, z, c) Ctx.t ->
    n D.t ->
    (mode, kinetic) value Lazy.t ->
    ((n, mode, kinetic) modal_value_cube, b) Vec.t ->
    ((D.zero, n, n, (mode, kinetic) modal_value) TubeOf.t, b) Vec.t ->
    (n, mode, c, kinetic) any_modal_term_cube list =
 fun ctx n fnty xs tyargs ->
  match (xs, tyargs) with
  | [], [] -> []
  | Modal (xfilter, x) :: xs, tyargs :: tyargs_rest -> (
      (* The constructor's function-type value must be a pi-type; we read back the argument at its domain (instantiated at the corresponding arguments of the lower-dimensional constructors, which are also read back to form the boundary of the argument cube) and continue with the codomain applied to the argument cube. *)
      let (Viewed_pi { x = _; filter; doms; cods }) = view_pi "readback_at_pi" n (Lazy.force fnty) in
      let pimod = Modality.filter_modality filter in
      let xmodality = Modality.filter_modality xfilter in
      match Modality.compare xmodality pimod with
      | Neq -> fatal (Modality_mismatch (`Internal, "readback_at_pi", xmodality, pimod))
      | Eq ->
          let Eq = Modality.filter_uniq xfilter filter in
          let (Locked (cplus, lctx)) = Ctx.lock ctx pimod in
          let x = CubeOf.find_top x in
          let tyarg = modal_boundary_tube "readback_at_pi" n filter doms tyargs in
          let tms = TubeOf.mmap { map = (fun _ [ arg ] -> readback_nf lctx arg) } [ tyarg ] in
          let ity = inst (CubeOf.find_top doms) tyarg in
          let argcube = TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x) in
          let (BindFam b) = BindCube.find_top cods in
          Modal
            ( xfilter,
              cplus,
              TubeOf.plus_cube tms (CubeOf.singleton (readback_at Kinetic lctx x ity)) )
          :: readback_at_pi ctx n (lazy (apply_binder_term b filter argcube)) xs tyargs_rest)

(* To readback an environment, since readback is type-directed we need the types of *all* the terms in it, which is to say its codomain context.  We store this as a Termctx since we need to evaluate and instantiate the types at the previous terms in the environment as we go. *)
and readback_env : type mode n a b c d.
    (mode, a, b) Ctx.t -> (mode, n, d) Value.env -> (mode, c, d) termctx -> (mode, b, n, d) Term.env
    =
 (* The permutation in a context only acts on the raw length, not the checked length which is what matches the env, so we can ignore it here. *)
 fun ctx env (Permute (_, envctx)) ->
  readback_ordered_env ctx env envctx

and readback_ordered_env : type mode n a b c d.
    (mode, a, b) Ctx.t ->
    (mode, n, d) Value.env ->
    (mode, c, d) ordered_termctx ->
    (mode, b, n, d) Term.env =
 fun ctx env envctx ->
  match envctx with
  | Emp mode -> Emp (mode, dim_env env)
  (* A weakening entry contributes nothing to the environment, so we skip it. *)
  | Weaken (envctx, _) -> readback_ordered_env ctx env envctx
  | Ext (envctx, entry, _) -> (
      match entry with
      | Vis { plus_lock = dplus; bindings; filter = filtered; _ }
      | Invis { plus_lock = dplus; bindings; filter = filtered; _ } ->
          let modality = plus_lock_modality dplus in
          (* The dimension n of the environment gets filtered to m. *)
          let n = dim_env env in
          let (Has_filter filter) = Modality.filter modality n in
          let m = Modality.filtered n filter in
          (* The dimension of the context entry is k. *)
          let k = dim_entry entry in
          (* The dimension of the cube in the environment must therefore be m+k. *)
          let (Plus m_k) = D.plus k in
          let mk = D.plus_out m m_k in
          (* We act by a sface_of_filter to reduce the dimension of the environment to m, so that we can get an (m+k)-dimensional cube out of it. *)
          let aenv = act_env env (opt_op_of_opt_sface (Modality.sface_of_filter n filter)) in
          (* We get the top entry (Now) from the environment we're reading back.  We can't just match it against Ext or LazyExt because it could have other lazy operations applied to it like Shift, Unshift, Permute, etc. *)
          (* Since no keys are stripped here, the prekey transport modality is just the entry's annotating modality. *)
          let (Looked_up { act; op; entry = xs; pre }) =
            lookup_cube aenv m_k modality modality Now (id_opt_op mk) in
          (* As usual, the missing endpoints in sface_of_filter should be canceled by degeneracies in the non-unary case. *)
          let (Op (fc, fd)) =
            op_of_opt op <|> Anomaly "unexpected missing endpoint in readback_ordered_env" in
          (* We are reading back bindings that were defined under a modality, so they are defined in a locked context. *)
          let (Locked (bplus, lctx)) = Ctx.lock ctx modality in
          (* We also analogously key the environment we're reading back, for purposes of evaluating types. *)
          let lenv = key_id_env aenv dplus in
          (* We apply the accumulated operators, degeneracies, and any prekey action to the entry we found. *)
          let xs = act_cube { act } (CubeOf.subcube fc xs) fd pre in
          (* Now we read back all the terms and types in that environment entry.  We record the normal forms in a hashtbl as we go, to use as instantiation arguments to types of higher-dimensional terms. *)
          let xtytbl = Hashtbl.create 10 in
          let tmxs =
            CubeOf.mmap
              {
                map =
                  (fun fab [ tm ] ->
                    let (SFace_of_plus (_, fb, fa)) = sface_of_plus m_k fab in
                    (* The type to read back at comes from the top entry in the codomain context.  This is a term, so we have to evaluate it to get a value before reading back at it.  We evaluate it in our given environment, so that it can use the terms to the left and also lower-dimensional terms in the current entry.  We have to lock that environment to make those latter entries available. *)
                    let ty = (CubeOf.find bindings fa).ty in
                    let ety = eval_term (act_env lenv (opt_op_of_sface fb)) ty in
                    (* Now we instantiate it at the lower-dimensional normal forms that we already computed. *)
                    let ty =
                      inst ety
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fb))
                           {
                             build =
                               (fun fc ->
                                 Hashtbl.find xtytbl (SFace_of (comp_sface fb (sface_of_tface fc))));
                           }) in
                    (* We use this computed type to make a normal form, and record it in the hashtbl. *)
                    Hashtbl.add xtytbl (SFace_of fb) { tm; ty = Lazy.from_val ty };
                    (* Finally, we read back the term in that instantiated type. *)
                    readback_at Kinetic lctx tm ty);
              }
              [ xs ] in
          (* For the recursive call, we remove the entry we found. *)
          let tmenv = readback_ordered_env ctx (remove_top env) envctx in
          Ext
            {
              env = tmenv;
              plus = m_k;
              values = Term.Modal (modality, bplus, tmxs);
              filter;
              filtered;
            })
  | Lock _ -> (
      (* We remove as many locks as there are at the end of the codomain context, since keys in the environment could have composite modalities as their domain. *)
      let (Ordered_remove_locks (envctx, plus_src, no_locks)) =
        Termctx.ordered_remove_locks envctx in
      (* Then we remove all the corresponding keys from the environment being read back. *)
      let (Restrict_keys (env, extra, mu12, cell, pre)) = restrict_keys_plus_lock env plus_src in
      (* Since we removed a maximal run of locks, and a key can only span locks, the split can never land in the middle of a key here, so there is nothing extra. *)
      match (extra, no_locks) with
      | Plus_lock (Suc _, _), _ -> .
      | Plus_lock (Zero _, Zero), _ -> (
          let Eq = Modality.comp_uniq mu12 (Modality.id_comp (plus_lock_modality plus_src)) in
          match Modalcell.compare_id pre with
          | Eq ->
              (* If there is no prekey action, we just remove the target of the composite key cell from the context we're reading back *into*, and read back the residual environment as a keyed term environment. *)
              let (Remove_lock (ctx, plus_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt cell) in
              Term.Key { env = readback_ordered_env ctx env envctx; cell; plus_src; plus_tgt }
          | Neq ->
              (* A prekey action mediates between a context locked by its vertical source (where the keyed value was created, e.g. behind a parametric locker's locks) and one locked by its vertical target (the actual ambient context, e.g. after the locker's counit discharged those locks).  So before removing the target of the key cell, we remove the target of the prekey from the context and re-lock it with the prekey's source, recording both in the term-level Prekey. *)
              let (Remove_lock (ctx, pre_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt pre) in
              let (Locked (pre_src, ctx)) = Ctx.lock ctx (Modalcell.vsrc pre) in
              let (Remove_lock (ctx, plus_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt cell) in
              Prekey
                {
                  env =
                    Term.Key { env = readback_ordered_env ctx env envctx; cell; plus_src; plus_tgt };
                  cell = pre;
                  plus_src = pre_src;
                  plus_tgt = pre_tgt;
                }))

(* Read back a context of values into a context of terms. *)

and readback_bindings : type mode a b n.
    (mode, a, b) Ctx.t -> (n, mode Binding.t) CubeOf.t -> (n, (mode, b) binding) CubeOf.t =
 fun ctx vbs ->
  CubeOf.mmap
    {
      map =
        (fun _ [ b ] ->
          match Binding.level b with
          | Some _ ->
              ({ tm = None; ty = readback_val ctx (Lazy.force (Binding.value b).ty) }
                : (mode, b) binding)
          | None ->
              {
                tm = Some (readback_nf ctx (Binding.value b));
                ty = readback_val ctx (Lazy.force (Binding.value b).ty);
              });
    }
    [ vbs ]

and readback_ordered_ctx : type mode a b. (mode, a, b) Ctx.Ordered.t -> (mode, a, b) ordered_termctx
    = function
  | Emp mode -> Emp mode
  | Snoc (rest, e, af) as ctx -> (
      let ctx = Ctx.of_ordered ctx in
      match e with
      | Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus; filter } ->
          let modality = Modality.filter_modality filter in
          let top = Binding.value (CubeOf.find_top bindings) in
          (* Fields as illusory variables are only used when typechecking records, which have substitution dimension 0 and can have no higher fields, so as field insertion we can use the identity on zero. *)
          let fins = ins_zero D.zero in
          let (Locked (plus_lock, lctx)) = Ctx.lock ctx modality in
          let fields =
            Bwv.map
              (fun (f, x) ->
                let fldty =
                  readback_val lctx
                    (tyof_field
                       (Modality.id (Ctx.mode lctx))
                       (Ok top.tm) (Lazy.force top.ty) f fins) in
                (f, x, fldty))
              fields in
          let bindings = readback_bindings lctx bindings in
          Ext
            ( readback_ordered_ctx rest,
              Vis { dim; plusdim; plus_lock; vars; bindings; hasfields; fields; fplus; filter },
              af )
      | Invis { filter; bindings; _ } ->
          let modality = Modality.filter_modality filter in
          (* Invisible variables are anonymous, but we can still record display hints from their types, since after readback the types are terms and the hints can no longer be computed on demand.  Since this only affects display, if anything goes wrong computing the type (e.g. the binding is an error placeholder) we just skip the hints. *)
          let hints =
            Reporter.try_with ~fatal:(fun _ -> no_hints) @@ fun () ->
            View.hints_of_ty (Lazy.force (Binding.value (CubeOf.find_top bindings)).ty) in
          let (Locked (plus_lock, lctx)) = Ctx.lock ctx modality in
          Ext
            ( readback_ordered_ctx rest,
              Invis { plus_lock; filter; bindings = readback_bindings lctx bindings; hints },
              af ))
  | Lock (ctx, lock) -> Lock (readback_ordered_ctx ctx, lock)
  | Weaken (ctx, code) -> Weaken (readback_ordered_ctx ctx, code)

and readback_ctx : type mode a b. (mode, a, b) Ctx.t -> (mode, a, b) termctx = function
  | Permute { perm; ctx; _ } -> Permute (perm, readback_ordered_ctx ctx)

(* Now we move on to readback of potential-only values like data, codata, match, and comatch. *)

(* ********** Readback of data types (for display only) ********** *)

(* Read back a datatype definition. *)
and readback_data : type mode a b m j ij.
    (mode, a, b) Ctx.t -> (mode, m, j, ij) Value.data_args -> (mode, b, potential) term =
 fun ctx { constrs; discrete; recursive; tyfam; hints; dim; indices } ->
  let ij = Fillvec.expected_length indices in
  (* Evaluate each constructor's stored function-type in its appropriately-dimensional environment and then read it back. *)
  let constrs = Abwd.mapi (readback_dataconstr ctx) constrs in
  let tyfam = readback_nf ctx (nf_of_neu (force_eval_term tyfam) "readback_data") in
  let data : (mode, b, potential) term =
    Canonical (Data { indices = ij; evaldim = dim; constrs; discrete; recursive; tyfam; hints })
  in
  (* Now we apply it to all the saved indices.  This requires the Potential form of App, which is not re-evaluable. *)
  let mode = Ctx.mode ctx in
  List.fold_left
    (fun t i ->
      App
        ( Potential,
          t,
          dim,
          Modality.filter_id mode dim,
          Modal
            ( Modality.id mode,
              plus_no_lock mode,
              CubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ i ] ) ))
    data (Fillvec.to_list indices)

(* Read back the type of a constructor. *)
and readback_dataconstr : type mode m a b.
    (mode, a, b) Ctx.t -> Constr.t -> (mode, m) dataconstr -> (mode, b, kinetic) term =
 fun ctx c (Dataconstr { env; ty }) ->
  let m = dim_env env in
  (* The evaluated, but uninstantiated, type. *)
  let ft = Norm.eval_term env ty in
  (* For a degenerate (higher-dimensional) datatype, we instantiate the resulting higher-dimensional pi-type at the lower-dimensional versions of the constructor itself.  Here is the boundary at which to instantiate. *)
  let tbl = Hashtbl.create 10 in
  let boundary =
    TubeOf.build D.zero (D.zero_plus m)
      {
        build =
          (fun fa ->
            let fa = sface_of_tface fa in
            (* The constructor's function-type at this face, obtained by evaluating the same term in a faced environment, instantiated at the lower faces of the constructor that we have already computed. *)
            let fty =
              Norm.inst
                (Norm.eval_term (act_env env (opt_op_of_sface fa)) ty)
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc -> Hashtbl.find tbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            (* The constructor-function at this face, built at this face's dimension and type by eta-expanding the constructor. *)
            let tm =
              Norm.eval_term (Ctx.env ctx) (readback_constr_function ctx (dom_sface fa) c Emp fty)
            in
            let nf = { tm; ty = Lazy.from_val fty } in
            Hashtbl.add tbl (SFace_of fa) nf;
            nf);
      } in
  readback_val ctx (Norm.inst ft boundary)

(* Build the term of the eta-long constructor "λ⁽ⁿ⁾ args. c⁽ⁿ⁾ args" at dimension n, over the display context, given the n-dimensional function-type value ft of the constructor. *)
and readback_constr_function : type mode lev e n.
    (mode, lev, e) Ctx.t ->
    n D.t ->
    Constr.t ->
    (n, mode, kinetic) modal_value_cube Bwd.t ->
    (mode, kinetic) value ->
    (mode, e, kinetic) term =
 fun ctx n c args ft ->
  match view_type ft "readback_constr_function" with
  | Canonical (_, Pi { x; filter; doms; cods }, ins, tyargs) -> (
      (* Walk the pi-type exactly as in the eta-expanding readback of a term at a pi-type (readback_at, ~eta case), introducing a cube of fresh variables for each argument.  We accumulate those variables as we go. *)
      let Eq = eq_of_ins_zero ins in
      match D.compare (BindCube.dim cods) n with
      | Neq -> fatal (Dimension_mismatch ("readback_constr_function", BindCube.dim cods, n))
      | Eq ->
          let modality = Modality.filter_modality filter in
          let name = View.fill_hints doms x in
          let newargs, newnfs = dom_vars ctx modality doms in
          let (Any_ctx newctx) =
            Ctx.variables_vis ctx (Modality.filter_idempotent filter) name newnfs in
          let output = tyof_app cods tyargs filter newargs in
          let body =
            readback_constr_function newctx n c (Snoc (args, Modal (filter, newargs))) output in
          Term.Lam (name, n, filter, body))
  | _ ->
      (* ft is now the datatype instance; the constructor applied to all the abstracted argument variables, read back at this fully-extended context.   We read back the accumulated argument variables at the fully-extended context to form the constructor's argument spine. *)
      let cargs =
        Bwd_extra.to_list_map
          (fun (arg : (n, mode, kinetic) modal_value_cube) ->
            let (Modal (filter, argcube)) = arg in
            let (Locked (plus, lctx)) = Ctx.lock ctx (Modality.filter_modality filter) in
            Term.Modal
              (filter, plus, CubeOf.mmap { map = (fun _ [ v ] -> readback_val lctx v) } [ argcube ]))
          args in
      Term.Constr (c, n, cargs)

(* ********** Readback of codata types (for display only) ********** *)

(* Raise a normal into a context degenerated by 'r, by reading it back and re-evaluating it in the degenerating environment, instantiating its type at the correspondingly raised faces. *)
and degenerate_normal : type mode a b r.
    (mode, a, b) Ctx.t -> (mode, r, b) env -> r D.t -> mode normal -> mode normal =
 fun ctx degenv r nf ->
  let ctm = readback_nf ctx nf in
  let tm = eval_term degenv ctm in
  let cty = readback_val ctx (Lazy.force nf.ty) in
  let ity = eval_term degenv cty in
  let argstbl = Hashtbl.create 10 in
  let tyargs =
    TubeOf.build D.zero (D.zero_plus r)
      {
        build =
          (fun fa ->
            let faenv = act_env degenv (opt_op_of_sface (sface_of_tface fa)) in
            let fatm = eval_term faenv ctm in
            let faty =
              inst (eval_term faenv cty)
                (TubeOf.build D.zero
                   (D.zero_plus (dom_tface fa))
                   {
                     build =
                       (fun fb ->
                         Hashtbl.find argstbl
                           (SFace_of (comp_sface (sface_of_tface fa) (sface_of_tface fb))));
                   }) in
            let nf = { tm = fatm; ty = Lazy.from_val faty } in
            Hashtbl.add argstbl (SFace_of (sface_of_tface fa)) nf;
            nf);
      } in
  { tm; ty = Lazy.from_val (inst ity tyargs) }

(* Raise a whole cube of values into a context degenerated by 'r, in the same way: the value at the (fa,fb) face of the result is the fa-degeneration of the value at the fb face.  No types are involved, so unlike degenerate_normal there is nothing to instantiate. *)
and degenerate_value_cube : type mode a b r n rn.
    (mode, a, b) Ctx.t ->
    (mode, r, b) env ->
    (r, n, rn) D.plus ->
    (n, (mode, kinetic) value) CubeOf.t ->
    (rn, (mode, kinetic) value) CubeOf.t =
 fun ctx degenv r_n vals ->
  let ctms = CubeOf.mmap { map = (fun _ [ v ] -> readback_val ctx v) } [ vals ] in
  CubeOf.build
    (D.plus_out (dim_env degenv) r_n)
    {
      build =
        (fun fab ->
          let (SFace_of_plus (_, fa, fb)) = sface_of_plus r_n fab in
          eval_term (act_env degenv (opt_op_of_sface fa)) (CubeOf.find ctms fb));
    }

(* Read back a codatatype or record type.  Non-projectable higher-field instances are displayed in a context degenerated by their remaining dimensions.  The result is a Canonical (Codata …), but at the evaluation dimension of the value rather than zero: its fields are the field instances of a possibly-degenerated codatatype, one per partial bijection between that dimension and the field's intrinsic dimension, whereas a codatatype produced by typechecking always has evaluation dimension zero and one instance per field.  Its intrinsic (Gel) dimension is that of the value being displayed.  The result carries no fibrancy (see Term.codata_fibrancy_option), so it is display-only: evaluating it is an anomaly. *)
and readback_codata : type mode a b cm cn ca cet iu ii iout.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) Value.value ->
    (* The instantiation arguments of the value being displayed: empty if it is an uninstantiated (higher-dimensional) codatatype, a full tube if it is a type. *)
    (iu, ii, iout, mode normal) TubeOf.t ->
    (mode, cm, cn, ca, cet) Value.codata_args ->
    (D.zero, iu, iu, mode normal) TubeOf.t ->
    (* The splitting of the value's total dimension into its evaluation dimension and its intrinsic (Gel) dimension.  Only the sum of the two matters to the self variable and the field types, but a higher field forces the intrinsic dimension to be zero, exactly as it does for a declared codatatype.  This sum is the fact that the stored insertion on the codata is the identity; if it isn't, then it isn't actually a codata, and is handled by readback_permuted_codata. *)
    (cm, cn, iout) D.plus ->
    (mode, b, potential) term =
 fun ctx tm insargs codata_args boundary cm_cn ->
  let mk = TubeOf.uninst insargs in
  let evaldim = dim_env codata_args.env in
  let dom = TubeOf.plus_cube (val_of_norm_tube boundary) (CubeOf.singleton tm) in
  let fields =
    Bwd.fold_left
      (fun (acc : (mode * b * cm * iout * cet) Term.CodatafieldAbwd.t) entry ->
        match readback_codatafield ctx mk dom evaldim insargs codata_args.env cm_cn entry with
        | None -> acc
        | Some entry -> Bwd.Snoc (acc, entry))
      Bwd.Emp codata_args.fields in
  Term.Canonical
    (Codata
       {
         eta = codata_args.eta;
         opacity = codata_args.opacity;
         hints = codata_args.hints;
         evaldim;
         dim = D.plus_right cm_cn;
         plusdim = cm_cn;
         fields;
         fibrancy = None;
         is_glue = None;
       })

(* Read back one field of a codatatype value being displayed, as an entry of readback_codata's result, or None if the field disappears because its left adjoint filters the instantiated dimension nontrivially (exactly as it does for projection and equality-checking).  ctx, mk, dom, evaldim, insargs, codataenv and cm_cn are those built by readback_codata: dom is the self-variable's boundary cube (the instantiation arguments plus the displayed value on top), evaldim is the codatatype's evaluation dimension, and codataenv and cm_cn are the codatatype's own environment and dimension splitting, which the field's stored type is evaluated over. *)
and readback_codatafield : type mode a b cm cn ca cet iu ii iout.
    (mode, a, b) Ctx.t ->
    iu D.t ->
    (iu, (mode, kinetic) Value.value) CubeOf.t ->
    cm D.t ->
    (iu, ii, iout, mode normal) TubeOf.t ->
    (mode, cm, ca) env ->
    (cm, cn, iout) D.plus ->
    (mode * ca * D.zero * cn * cet) Term.CodatafieldAbwd.entry ->
    (mode * b * cm * iout * cet) Term.CodatafieldAbwd.entry option =
 fun ctx mk dom evaldim insargs codataenv cm_cn
     (Entry
        (type i)
        ((fld, Codatafield (self, (Adjunction { left; right; unit; _ } as adj), fld_plus_lock, cf)) :
          i Field.t * (i, mode * ca * D.zero * cn * cet) Term.Codatafield.t)) ->
  let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
  let (Has_filter lfilter) = Modality.filter left (D.plus_out mk (TubeOf.plus insargs)) in
  match Modality.filter_is_trivial (D.plus_out mk (TubeOf.plus insargs)) lfilter with
  | None -> None
  | Some Eq ->
      (* As in check_codata, each field's type is displayed in the ambient context locked by the field's right adjoint and then extended by the self variable, annotated by its left adjoint; so we build that context per field.  The self variable's *type* is the codatatype transported behind those locks along the adjunction unit, which is where a variable annotated by the left adjoint has its type; and the instantiation arguments, being its boundary faces there, are transported along with it.  (For an ordinary non-modal field the unit is an identity cell and this is a no-op.)  So the entire self cube, variables and instantiation arguments alike, consists of values of that self-extended context, which is also where the field's type is computed and read back. *)
      Some
        (let tys = CubeOf.mmap { map = (fun _ [ v ] -> act_value v (id_deg D.zero) unit) } [ dom ] in
         let _, freshself = dom_vars lctx left tys in
         (* The boundary of a degenerate codatatype behaves like parameters, not indices as for a degenerate datatype: it is the *instantiated* form that one defines elements of by comatching.  So a codatatype value that has been instantiated is displayed as it is, showing the types of the fields such a comatch must supply.  Thus the self cube's boundary faces, in the dimensions the instantiation supplied, are the instantiation arguments themselves, bound as values rather than as fresh variables exactly as they are for the self value of a comatch being checked, so that the field types display in terms of them; only the remaining dimensions get fresh variables, whose top face has the fully instantiated codatatype as its type. *)
         let selfbindings =
           TubeOf.plus_cube
             (TubeOf.mmap
                {
                  map =
                    (fun _ [ nf ] ->
                      Ctx.Binding.make None
                        {
                          tm = act_value nf.tm (id_deg D.zero) unit;
                          ty = lazy (act_value (Lazy.force nf.ty) (id_deg D.zero) unit);
                        });
                }
                [ insargs ])
             freshself in
         let sctx = Ctx.cube_vis lctx (Modality.filter_idempotent lfilter) None selfbindings in
         let selfnfs = CubeOf.mmap { map = (fun _ [ b ] -> Ctx.Binding.value b) } [ selfbindings ] in
         match cf with
         (* We display the type as it was *declared*: evaluated over the codatatype's own environment, keyed behind the right-adjoint lock and left there un-keyed (~key:`Nokey), exactly as check_codata checked it.  Hence we call tyof_lower_codatafield directly, supplying that environment and the self cube, rather than going through tyof_field, which recovers both from the *type* of an ambient term being projected; here there is no ambient term, only the self variable of the context we are displaying in. *)
         | Lower fldty ->
             let ety =
               tyof_lower_codatafield
                 (`Ok (val_of_norm_cube selfnfs))
                 (TubeOf.boundary selfnfs) fld adj fld_plus_lock fldty codataenv evaldim cm_cn
                 ~key:`Nokey in
             let ty = readback_val sctx ety in
             Entry (fld, Codatafield (self, adj, plus_lock, Lower ty))
         | Higher (fldtermctx, fldtys) ->
             (* A codatatype with a higher field has intrinsic dimension zero, so its whole dimension, at which the self-variable cube lives and at which the instances of the field are indexed, is its evaluation dimension. *)
             let Eq = D.plus_uniq cm_cn (D.plus_zero evaldim) in
             let tys =
               readback_higher_codatafield ctx codataenv fld_plus_lock fldtermctx fldtys
                 (CubeOf.dim selfnfs) fld adj selfnfs sctx in
             Entry (fld, Codatafield (self, adj, plus_lock, Higher (readback_ctx lctx, tys))))

(* Read back the instances of one higher field of a codatatype value being displayed, as the pbijmap of types that Codatafield.Higher stores: one entry per partial bijection between the codatatype's evaluation dimension m and the field's intrinsic dimension i.  The self variable, its cube, and the context they live in are those built by readback_codata, while the environment, lock, termctx and stored types are those of the codatatype value being displayed; the ambient context is needed only to degenerate for a non-projectable instance. *)
and readback_higher_codatafield : type mode a b ca m i f g gmode ag bg d raw.
    (mode, a, b) Ctx.t ->
    (mode, m, ca) env ->
    (ca, mode, g, gmode, ag) plus_lock ->
    (gmode, d, ag) termctx ->
    (D.zero, i, gmode * (ag, (f, D.zero) dim_entry) snoc) Term.FieldtypePbijmap.t ->
    m D.t ->
    i Field.t ->
    (mode, f, g, gmode) Modalcell.adjunction ->
    (m, mode normal) CubeOf.t ->
    (gmode, raw, (bg, (f, m) dim_entry) snoc) Ctx.t ->
    (m, i, gmode * (bg, (f, m) dim_entry) snoc) Term.FieldtypePbijmap.t =
 fun ctx codataenv plus_lock fldtermctx fldtys m fld adj selfnfs sctx ->
  let left = Modalcell.adj_left adj in
  (* The codatatype whose value we are displaying was produced by typechecking, so it has evaluation dimension zero and its field has just its declared type. *)
  let (Fieldtype (ic0, fldty)) = declared_fieldtype fldtys in
  Term.FieldtypePbijmap.build m (Field.dim fld)
    {
      build =
        (fun (type r)
          (Pbij (fldins, fldshuf) : (m, i, r) pbij)
          :
          (r, gmode * (bg, (f, m) dim_entry) snoc) Term.FieldtypeFam.t
        ->
          match D.compare_zero (left_shuffle fldshuf) with
          | Zero ->
              (* Projectable instance: read back in the locked, self-extended context, as for a lower field, with a trivial degeneration and hence no remaining dimensions for the self cube to be degenerated by.  As there, we display the type as it was *declared*, computed from the codatatype's own environment and left un-keyed (~key:`Nokey). *)
              let Eq = eq_of_zero_shuffle fldshuf in
              let ety =
                tyof_higher_codatafield
                  (`Ok (val_of_norm_cube selfnfs))
                  (TubeOf.boundary selfnfs) (D.zero_plus m) fld adj codataenv fldins ~shuf:Trivial
                  plus_lock fldtermctx ic0 fldty ~key:`Nokey in
              Fieldtype (Plusmap.zerol (Ctx.tctx sctx), readback_val sctx ety)
          | Pos _ ->
              (* Non-projectable instance: degenerate by the remaining dimensions and compute the field type there, recording the degeneration plus-map.  The codatatype's parameters are degenerated by the shuffleable, in the ambient context; the self variable and its boundary we degenerate here, in the self-extended context locked by the left adjoint, which is where a variable annotated by that adjoint is accessible.  Both degenerations assign the same levels to the ambient variables, since degctx assigns levels by position. *)
              let r = left_shuffle fldshuf in
              let (Degctx (plusmap, dsctx, sdegenv)) = degctx sctx r in
              let (Degctx (_, _, degenv)) = degctx ctx r in
              let shuf =
                Nontrivial
                  {
                    shuffle = fldshuf;
                    deg_env =
                      (fun adj tctx r_k e ->
                        let (Locked (plus, lctx)) = Ctx.lock ctx (Modalcell.adj_right adj) in
                        eval_env (key_id_env degenv plus) r_k (readback_env lctx e tctx));
                  } in
              let (Locked (fplus, flctx)) = Ctx.lock sctx left in
              let fdegenv = key_id_env sdegenv fplus in
              let (Plus r_m) = D.plus m in
              let values =
                `Ok
                  (degenerate_value_cube flctx fdegenv r_m
                     (CubeOf.mmap { map = (fun _ [ nf ] -> nf.tm) } [ selfnfs ])) in
              let tyargs =
                TubeOf.mmap
                  { map = (fun _ [ nf ] -> degenerate_normal flctx fdegenv r nf) }
                  [ TubeOf.boundary selfnfs ] in
              let ety =
                tyof_higher_codatafield values tyargs r_m fld adj codataenv fldins ~shuf plus_lock
                  fldtermctx ic0 fldty ~key:`Nokey in
              Fieldtype (plusmap, readback_val dsctx ety));
    }

(* Read back a codatatype value whose insertion is *not* the identity, where a Gel-dimension has been permuted with evaluation dimensions.  Such a value is no longer a record type at all: its fields can't be projected, and there is no self-variable cube in the order in which the fields were declared.  But it is the permutation of a value that is one, so we un-permute it, read that back as a codatatype, and apply the permutation to the result as a degeneracy.  If it is instantiated, we first un-instantiate entirely, then re-instantiate afterwards.  Because a permuted codatatype is not a codatatype, we can't push the permutation or instantiation arguments inside the field types. *)
and readback_permuted_codata : type mode a b m k mk e n.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (m, k, mk, mode normal) TubeOf.t ->
    (mk, e, n) insertion ->
    (mode, b, potential) term =
 fun ctx neutral tyargs ins ->
  let mode = Ctx.mode ctx in
  match D.compare_zero (TubeOf.inst tyargs) with
  | Pos _ ->
      let uninst = uninstantiate mode neutral in
      Inst
        ( Potential,
          readback_permuted_codata ctx uninst.tm (TubeOf.empty (TubeOf.out tyargs)) ins,
          TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ tyargs ] )
  | Zero -> (
      let (Perm_to p) = perm_of_ins ins in
      let pinv = deg_of_perm (perm_inv p) in
      match act_value neutral pinv (Modalcell.id2 mode) with
      | Neu { value; ty = pty; _ } as pneutral -> (
          (* We basically go back to the Canonincal case of readback_at. *)
          match (force_eval value, view_type (Lazy.force pty) "readback_permuted_codata") with
          | ( Val (Canonical { canonical = Codata pargs; ins = pins; tyargs = ptyargs; _ }),
              Canonical (_, UU (_, pmk), pins0, pboundary) ) -> (
              let Eq = eq_of_ins_zero pins0 in
              match (D.compare (TubeOf.uninst ptyargs) pmk, is_id_ins pins) with
              | Eq, Some cm_cn ->
                  Act
                    ( Potential,
                      readback_codata ctx pneutral ptyargs pargs pboundary cm_cn,
                      deg_of_perm p,
                      (`Type, `Canonical) )
              | Neq, _ ->
                  fatal
                    (Dimension_mismatch ("readback_permuted_codata", TubeOf.uninst ptyargs, pmk))
              | _, None ->
                  fatal
                    (Anomaly "readback_permuted_codata: unpermuted insertion is not the identity"))
          | _ -> fatal (Anomaly "readback_permuted_codata: unpermuted value has wrong shape"))
      | _ -> fatal (Anomaly "readback_permuted_codata: unpermuted value is not a neutral"))

(* Un-instantiate a type value: strip the instantiation off the end of its neutral spine, and off its canonical value, returning the whole-dimensional type that was instantiated, as a normal.  A value carrying no instantiation is returned unchanged, which is what bottoms out the recursion below.  The uninstantiated type's own type is not stored anywhere -- inst computes the instantiated type from it and keeps only the spine -- so we rebuild it: a universe of the whole dimension, instantiated at the uninstantiated type's boundary.  That boundary is exactly what we are stripping off, in the two halves that a full tube splits into: its outer part is the *types* of the instantiation arguments, and its inner part (empty unless the instantiation was partial) is the arguments of the universe that the instantiated type itself belongs to.  Both arrive instantiated in their turn -- what we have of the boundary of "(Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,)" is "Gel A B R a₀ b₀" and "Id A a₀ a₁", where we want "Gel A B R" and "Id A" -- so we un-instantiate them recursively.  The recursion is on dimension, since each of them is lower-dimensional than the whole. *)
and uninstantiate : type mode. mode Mode.t -> (mode, kinetic) value -> mode normal =
 fun mode ty ->
  match view_term ty with
  | Neu { head; args = Inst (base_args, _, insargs); value; ty = instty } -> (
      match view_type (Lazy.force instty) "uninstantiate" with
      | Canonical (_, UU (_, umk), uins, uargs) -> (
          let Eq = eq_of_ins_zero uins in
          (* The universe the instantiated type belongs to has exactly its uninstantiated dimensions. *)
          match D.compare umk (TubeOf.uninst insargs) with
          | Neq -> fatal (Dimension_mismatch ("uninstantiate", umk, TubeOf.uninst insargs))
          | Eq ->
              let outer =
                TubeOf.mmap
                  { map = (fun _ [ nf ] -> uninstantiate mode (Lazy.force nf.ty)) }
                  [ insargs ] in
              let inner =
                TubeOf.mmap { map = (fun _ [ nf ] -> uninstantiate mode nf.tm) } [ uargs ] in
              let boundary = TubeOf.plus_tube (TubeOf.plus insargs) outer inner in
              let uty = lazy (inst (universe mode (TubeOf.out insargs)) boundary) in
              {
                tm = Neu { head; args = base_args; value = uninstantiate_value value; ty = uty };
                ty = uty;
              })
      | _ -> fatal (Anomaly "uninstantiating a type whose type is not a universe"))
  (* Nothing to strip: the value is already uninstantiated, and carries its own type. *)
  | Neu { ty = uty; _ } -> { tm = ty; ty = uty }
  | _ -> fatal (Anomaly "uninstantiating a non-neutral type")

(* The value of an un-instantiated neutral: a canonical type with its instantiation arguments emptied out, as eval_codata and friends produce it.  Anything else -- an axiom's Unrealized, say -- is unchanged by instantiation and so is left alone. *)
and uninstantiate_value : type mode. (mode, potential) lazy_eval -> (mode, potential) lazy_eval =
 fun value ->
  match force_eval value with
  | Val (Canonical { mode; canonical; ins; tyargs; fields; inst_fields = _ }) ->
      ready
        (Val
           (Canonical
              {
                mode;
                canonical;
                ins;
                tyargs = TubeOf.empty (TubeOf.out tyargs);
                fields;
                inst_fields = Some fields;
              }))
  | _ -> value

(* Given a multi-argument type family, and the type *of* that type family, both as values, and a context for them, compute the type of type families dependent *on* that family, as a term.  For example, if the arguments are

   x y z ↦ D x y z
   (x : A) (y : B x) (z : C x y) → Type

(as values), then the output will be

   (x : A) (y : B x) (z : C x y) (w : D x y z) → Type

(as a term).  However, although the indices of a datatype family themselves must be zero-dimensional, the type families involved here could be higher-dimensional, because they come from an *evaluation* of that datatype family which could be a higher-dimensional version of it.  In that case, the arguments are flattened out to a zero-dimensional family in the return value, so for instance if given

   x ⤇ B₂ x.2
   (x₀ : A₀) (x₁ : A₁) (x₂ : A₂ x₀ x₁) ⇒ Id Type (B₀ x₀) (B₁ x₁)

then the output will be

   (x₀ : A₀) (x₁ : A₁) (x₂ : A₂ x₀ x₁) (y₀ : B₀ x₀) (y₁ : B₁ x₁) (y₂ : B₂ x₂) → Type

In the modal case, there is a window modality, say μ : p → q, the inputs are at mode p, with all arguments NON-MODAL because in the context of use this is a datatype family with its indices, and indices cannot be modal.  However, the output is at mode q, depending modally on its arguments, since that is the motive of a match with window μ:

   (x :μ| A) (y :μ| B x) (z :μ| C x y) (w :μ| D x y z) → Type_q
   
   
*)
(* This function belongs morally to typechecking -- it computes the type at which the motive of a dependent match is checked -- but it lives here, in the recursive readback chain, because it reads back the types of the family's arguments, and because the readback of a stuck match needs it too, to read back the stored motive. *)
and motive_of_family : type dom window mode a b.
    (mode, a, b) Ctx.t ->
    (dom, window, mode) Modality.t ->
    (dom, kinetic) value ->
    (dom, kinetic) value ->
    (mode, b, kinetic) term =
 fun ctx window tm ty ->
  (* The motive's pi-type domains are window-modal, so their dimension filter is the (zero-dimensional) filter of the window modality. *)
  let filter = Modality.filter_zero window in
  (* First we define some auxiliary modules and traversal functions. *)
  let module S = struct
    type 'a suc = ('a, (window, D.zero) dim_entry) snoc
  end in
  let module F = struct
    type ('left, 'c, 'any) t =
      | Ftm :
          ('left, mode, window, dom, 'lw) plus_lock * (dom, 'lw, kinetic) term
          -> ('left, 'c, 'any) t
  end in
  let module FCube = Icube (S) (F) in
  let module C = struct
    type 'b t = (mode, 'b) Ctx.any
  end in
  let module T = struct
    type 'c t = (mode, 'c, kinetic) term
  end in
  let module MC = FCube.Traverse (C) in
  let module MT = FCube.Traverse (T) in
  let folder : type left m any.
      (left, m, any) F.t ->
      (left, (window, D.zero) dim_entry) snoc T.t ->
      left T.t * (left, m, any) F.t =
   fun (Ftm (left_plus, dom)) cod ->
    ( Pi
        {
          x = singleton_variables D.zero (`Anon no_hints);
          filter;
          doms = Modal (window, left_plus, CubeOf.singleton dom);
          cods = CodCube.singleton (Cod (filter, cod));
        },
      Ftm (left_plus, dom) ) in
  let builder : type left n m.
      n variables ->
      (n, dom Binding.t) CubeOf.t ->
      (m, n) sface ->
      left C.t ->
      (left, m, b) MC.fwrap_left =
   fun x newnfs fa (Any_ctx ctx) ->
    let (Locked (plus_window, wctx)) = Ctx.lock ctx window in
    let v = CubeOf.find newnfs fa in
    let cv = readback_val wctx (Lazy.force (Binding.value v).ty) in
    let name =
      match find_variable fa x with
      | `Named _ as x -> x
      | `Anon _ -> `Anon (View.hints_of_ty (Lazy.force (Binding.value v).ty)) in
    let (Any_ctx newctx) =
      (* TODO: In the case of a cube variable, should we be annotating the variable names by their face somehow?  *)
      Ctx.variables_vis ctx filter (singleton_variables D.zero name) (CubeOf.singleton v) in
    Fwrap (Ftm (plus_window, cv), Any_ctx newctx) in
  (* We start by inspecting the type of the family passed. *)
  match view_type ty "motive_of_family" with
  | Canonical (_, Pi { x; filter = ffilter; doms; cods }, ins, tyargs) -> (
      (* The type family itself must be non-modal (any modal window is carried separately). *)
      match Modality.compare_id (Modality.filter_modality ffilter) with
      | Neq -> fatal (Anomaly "modal family in motive_of_family")
      | Eq ->
          let Eq = eq_of_ins_zero ins in
          let newvars, newnfs = dom_vars ctx window doms in
          (* We extend the context, not by the cube of types of newnfs, but by its elements one at a time as singletons.  This is because we want eventually to construct a 0-dimensional pi-type.  As we go, we also read back these types and store them to later take the pi-type over.  Since they are all in different contexts, and we need to keep track of the type-indexed checked length of those contexts to ensure the later pis are well-typed, we use an indexed cube indexed over Tctxs. *)
          let (Wrap (newdoms, Any_ctx newctx)) =
            MC.build_left (CubeOf.dim newnfs)
              { build = (fun fa ctx -> builder x newnfs fa ctx) }
              (Any_ctx ctx) in
          (* Now we recurse into the codomain of the pi-type, having applied the type family itself to the new variables we introduced. *)
          let newtm = apply_term tm ffilter newvars in
          let motive = motive_of_family newctx window newtm (tyof_app cods tyargs ffilter newvars) in
          (* Finally, we postprocess that result by adding the pi-type domains we computed for this argument. *)
          let motive, _ = MT.fold_map_right { foldmap = (fun _ x y -> folder x y) } newdoms motive in
          motive)
  | Canonical (_, UU _, _, tyargs) ->
      (* We've reached the end of the function domains in the type of our type family.  We thus have one more domain to abstract over: the datatype itself, which is now the *term* we were passed in this version, along with all its boundaries, which are the instantiation arguments of the universe it belongs to. *)
      let doms = TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm) in
      let _, newnfs = dom_vars ctx window doms in
      let m = CubeOf.dim newnfs in
      let (Wrap (newdoms, _)) =
        MC.build_left m
          { build = (fun fa ctx -> builder (singleton_variables m (`Anon no_hints)) newnfs fa ctx) }
          (Any_ctx ctx) in
      (* The result is a pi-type over all those domains, whose codomain is just the universe. *)
      let motive, _ =
        MT.fold_map_right
          { foldmap = (fun _ x y -> folder x y) }
          newdoms
          (UU (Ctx.mode ctx, D.zero)) in
      motive
  | _ -> fatal (Anomaly "non-family in motive_of_family")

(* The type at which to read back the body of one branch of a stuck match, computed from the match's stored motive.  Typechecking applied that motive to the branch's indices and constructor as zero-dimensional arguments, one for each face of the match dimension; but here it is evaluated in the environment the match is stuck in, so each of those argument positions instead takes a cube of that environment's dimension, namely the slice of the (total-dimensional) argument cube lying over that face.  A non-dependent motive is the type of every branch alike and takes no arguments at all.

   Evaluated in a degenerated environment, the motive computes a *family* of that dimension rather than a type, so we instantiate it at the boundary of the branch body, which we get by evaluating that body in the corresponding faces of its own environment; the type of each such face is the same family at that face, instantiated in turn at its boundary, so we build them up face by face as dom_vars does for the domains of a pi-type.  In a zero-dimensional environment the boundary is empty and the instantiation does nothing, leaving exactly the application of a zero-dimensional motive to singletons that typechecking performed.

   A branch body is a case tree, so its value at a face may be a case tree too rather than a term; then there is nothing to instantiate at and we give up on displaying the match (the caller catches this and falls back to the application spine). *)
and motive_branch_ty : type mode dom window a c k n kn.
    (dom, window, mode) Modality.t ->
    (mode, k, a) env ->
    (mode, a) Term.match_motive ->
    (k, n, kn) D.plus ->
    n D.t ->
    (kn, (dom, kinetic) value) CubeOf.t list ->
    (mode, k, c) env ->
    (mode, c, potential) term ->
    (mode, kinetic) value =
 fun window env motive plus_dim match_dim args benv body ->
  let env_dim = dim_env env in
  (* The motive evaluated at a face of that environment, applied to the faces of the arguments lying over it. *)
  let family : type j. (j, k) sface -> (mode, kinetic) value =
   fun fe ->
    let j = dom_sface fe in
    let fenv = act_env env (opt_op_of_sface fe) in
    match motive with
    | `Type t -> eval_term fenv t
    | `Family t -> (
        let (Has_filter fj) = Modality.filter window j in
        match D.compare (Modality.filtered j fj) j with
        | Neq ->
            fatal
              (Readback_at_wrong_type
                 "read back at a motive whose window modality filters dimensions away")
        | Eq ->
            let (Plus jplus) = D.plus match_dim in
            let fa = sface_plus_sface fe plus_dim jplus (id_sface match_dim) in
            List.fold_left
              (fun f arg -> apply_slices fj j jplus match_dim f (CubeOf.subcube fa arg))
              (eval_term fenv t) args) in
  let tbl = Hashtbl.create 10 in
  let boundary =
    TubeOf.build D.zero (D.zero_plus env_dim)
      {
        build =
          (fun fe ->
            let fs = sface_of_tface fe in
            let tm =
              match eval (act_env benv (opt_op_of_sface fs)) body with
              | Realize v -> v
              | _ -> fatal (Readback_at_wrong_type "a case tree at one of its boundary faces") in
            let ty =
              inst (family fs)
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fs))
                   {
                     build =
                       (fun fc -> Hashtbl.find tbl (SFace_of (comp_sface fs (sface_of_tface fc))));
                   }) in
            let nf = { tm; ty = Lazy.from_val ty } in
            Hashtbl.add tbl (SFace_of fs) nf;
            nf);
      } in
  inst (family (id_sface env_dim)) boundary

(* ********** Readback of stuck matches (for display only) ********** *)

(* Read back a stuck case tree, possibly applied to arguments: check_match_branches run backwards.  This is display-only output, like the readback of a canonical type: it is never re-typechecked or re-evaluated.  Reading back a stuck term can legitimately fail; in that case we return None here, causing the caller to fall back to showing the neutral spine.  *)
and readback_stuck : type mode a z hmode any.
    (mode, potential) readback_status ->
    (mode, z, a) Ctx.t ->
    (hmode, potential) head * (hmode, mode, any) apps ->
    (mode, kinetic) value ->
    (mode, a, potential) term option =
 fun status ctx pn ty ->
  (* Some failure modes are apparent immediately and cause readback_stuck_match to return None itself.  Others are noticed only later in reading back the bodies of match clauses, because the type we read them back at may only approximate the type it was checked at.  Those errors would be bugs otherwise, so they raise these fatal errors; but in this case we catch them and return None, leading to a fallback. *)
  Reporter.try_with ~fatal:(fun d ->
      match d.message with
      | Readback_at_wrong_type str ->
          no_display (Printf.sprintf "a stuck match with a branch body that is %s" str)
      | Degenerated_neutral_not_a_struct ->
          no_display "a stuck match with a branch that reaches a higher field"
      | Matching_wont_refine (str, _) -> no_display ("a stuck match with " ^ str)
      | _ -> fatal_diagnostic d)
  @@ fun () -> readback_stuck_match status ctx pn ty

(* For each constructor we invent fresh pattern variables from its stored function-type, with ext_pi, exactly as typechecking does; extend the stored environment by them, with take_args, exactly as evaluation does; evaluate the branch body there; and read it back in the context extended by the same variables.  The reconstructed branch carries ext_pi's own annotate and comp -- which name the pattern variables after the constructor's arguments -- and the identity permutation, rather than the stored ones, which are relative to the original checking context.

   We reconstruct only when the stuck spine is empty, which is exactly when the type we were handed is the type of the match itself rather than of something the match was applied to; with a nonempty spine there would be no type at which to read back the branch bodies.  We also reconstruct only a match: a stuck metavariable has no branches to show.  In every other case we return None and the caller falls back to the application spine.

   The pattern variables are *not* substituted into the type or the context, so for a match that refines its motive the branch bodies are read back at the unrefined type rather than at the refined one that typechecking used.  The two are definitionally equal in the branch, so where the unrefined type still exposes the canonical form that readback needs -- which is everything except a motive that is itself a stuck match -- the display is right.  Where it doesn't, readback raises, and we catch that and fall back to the application spine, exactly as if there had been no payload at all. *)
and readback_stuck_match : type mode a z hmode any.
    (mode, potential) readback_status ->
    (mode, z, a) Ctx.t ->
    (hmode, potential) head * (hmode, mode, any) apps ->
    (mode, kinetic) value ->
    (mode, a, potential) term option =
 fun status ctx (Stuck { env; tm = ctm; ins }, apps) ty ->
  match (status, ctm) with
  | ( Potential (Neu { head = head_head; args; _ }),
      Match { tm; window; plus_lock; dim = match_dim; motive; branches } ) -> (
      (* The match at the head end of the spine is displayed in our context locked by the field projections the spine crosses, and the spine is put back around it afterwards. *)
      let (Readback_apps (ctx, rewrap)) = readback_apps Potential ctx apps in
      (* The stored insertion, if any, should also be put back around the read-back match. *)
      let rewrap x =
        match is_id_ins ins with
        | Some _ -> rewrap x
        | None ->
            let (To p) = deg_of_ins ins in
            rewrap (Term.Act (Potential, x, p, (`Other, `Other))) in
      (* The discriminee is evaluated exactly as eval does it, in the environment keyed and filtered by the window modality. *)
      let env_dim = dim_env env in
      let (Has_filter fw) = Modality.filter window env_dim in
      let akenv =
        act_env (key_id_env env plus_lock)
          (opt_op_of_opt_sface (Modality.sface_of_filter env_dim fw)) in
      let (Plus plus_dim) = D.plus match_dim in
      let total_dim = D.plus_out (Modality.filtered env_dim fw) plus_dim in
      let disc = eval_term akenv tm in
      let disc_nf = nf_of_neu disc "discriminee of stuck match" in
      (* Similarly, the discriminee is read back in a context locked by the window modality. *)
      let (Locked (new_plus_lock, lctx)) = Ctx.lock ctx window in
      let disc_tm = readback_val lctx disc in
      (* The self a branch body is read back against must live at the mode of the match, not of the whole spine, so we take the neutral we were given and strip the spine's eliminations back off it. *)
      let (Any head_args) = strip_apps args apps <|> Anomaly "stuck match spine mismatch" in
      match view_type (Lazy.force disc_nf.ty) "readback_stuck_match" with
      | Canonical
          (type hmode mn m n)
          (( _,
             Data { dim = data_dim; constrs; indices = Filled data_indices; tyfam; _ },
             disc_ins,
             disc_tyargs ) :
            (hmode, kinetic) head * (_, m, n) canonical * (mn, m, n) insertion * _) -> (
          (* A datatype has intrinsic dimension zero, so its instantiation tube is at its substitution dimension. *)
          let Eq = eq_of_ins_zero disc_ins in
          let tyfam = nf_of_neu (force_eval_term tyfam) "check_var_match" in
          (* The dimension of the discriminee's datatype must be the stored match dimension plus the dimension of the environment we are stuck in. *)
          match D.compare data_dim total_dim with
          | Eq ->
              let open Monad.Ops (Monad.Maybe) in
              (* The type of the match itself.  The motive computes it, but only in a zero-dimensional environment: evaluated in a degenerated one it computes an uninstantiated family instead, and the boundary to instantiate it at consists of the matches at the faces of that environment, which are stuck case trees rather than values.  So a degenerated match takes the type it was handed, which is that of the match itself exactly when the spine is empty.  (Each *branch* type is still computed from the motive, since the boundary there consists of the branch bodies, which we can evaluate; see motive_branch_ty.) *)
              let* new_motive, match_ty =
                match (motive, empty_apps apps, D.compare_zero env_dim) with
                (* An explicit motive is a type family over the datatype's indices and the datatype itself.  Evaluated in the environment we are stuck in, it gives the type of the match, when applied to the discriminee's indices, instantiation arguments, and itself.  We also read it back, at the same type of type families that it was checked against, so that the displayed match shows it again in a "return" clause. *)
                | Some (`Family t), _, Zero ->
                    let emotive = eval_term env t in
                    let motive_ty =
                      eval_term (Ctx.env ctx)
                        (motive_of_family ctx window tyfam.tm (Lazy.force tyfam.ty)) in
                    let r = Vec.fold_left (apply_singleton_nfs window) emotive data_indices in
                    let r = apply_singleton_tube_nfs window r disc_tyargs in
                    Some
                      ( Some (`Family (readback_at Kinetic ctx emotive motive_ty)),
                        apply_term r (Modality.filter_zero window) (CubeOf.singleton disc) )
                (* A non-dependent match instead records one type, which is that of the match and of every branch alike.  There is no surface syntax for such a match other than the placeholder "return _ … _ ↦ _", which says nothing about the type, so we don't read it back. *)
                | Some (`Type t), _, Zero -> Some (None, eval_term env t)
                (* If the stuck match isn't applied to any arguments, then the overall type is also the type of the match. *)
                | _, Some Eq, _ -> Some (None, ty)
                | _, _, Zero -> no_display "an implicit stuck match applied to arguments"
                | _, _, Pos _ ->
                    no_display "a stuck match in a degenerated environment applied to arguments"
              in
              let new_branches =
                Constr.Map.mapi
                  (fun constr br ->
                    match br with
                    | Term.Branch { annotate; comp; perm; tm = body } ->
                        let (Dataconstr { env = cenv; ty = cty }) =
                          Abwd.find_opt constr constrs
                          <|> Anomaly "constructor missing from stuck match in readback" in
                        (* Fresh pattern variables, named as in the branch; ext_pi fills in the constructor's argument names for anonymous ones. *)
                        let (Wrap arity) = pi_arity cty in
                        let (Bplus plus_args) = Raw.Indexed.bplus arity in
                        let xs =
                          match Vec.of_list_length arity (annotate_names annotate) with
                          | Some names -> Raw.Indexed.Namevec.of_vec plus_args names
                          | None -> fatal (Anomaly "constructor argument length mismatch") in
                        let (Ext_pi
                               {
                                 ctx = branch_ctx;
                                 values = newvars;
                                 annotate = new_annotate;
                                 comp = new_comp;
                                 out;
                                 normals = _;
                               }) =
                          ext_pi ctx window cenv xs (Norm.eval_term cenv cty) in
                        (* We first try to refine the context and return type by rebinding the variable discriminee to the constructor, as when typechecking a variable match, except in environments rather than contexts.  This is not always possible, even for a match that was originally a variable, since a discriminee (or its indices or boundary) that was originally a free variable might have been substituted by something else. *)
                        Reporter.try_with
                          (fun () ->
                            (* Skip refining right away if we have an explicit motive or a non-dependent match. *)
                            (match motive with
                            | Some _ -> fatal (Matching_wont_refine ("explicit/nondep", None))
                            | None -> ());
                            (* We assemble a table of the variables to rebind to new values, checking along the way that they are all distinct and free. *)
                            let seen = Hashtbl.create 10 in
                            let new_vals = Hashtbl.create 10 in
                            (* First we add the index variables, rebinding them to their values from the discriminee's type. *)
                            let index_nfs =
                              indices_of_out "match branch" out total_dim (Vec.length data_indices)
                            in
                            let index_vals = Vec.map val_of_norm_cube index_nfs in
                            Vec.miter
                              (fun [ vs; cs ] ->
                                CubeOf.miter
                                  {
                                    it =
                                      (fun _ [ x; c ] ->
                                        let v = is_fresh ctx window seen x in
                                        Hashtbl.add new_vals v c);
                                  }
                                  [ vs; cs ])
                              [ data_indices; index_nfs ];
                            (* Then we add the discriminee and its boundary variables, and the constructor values to rebind them to. *)
                            let constr_vars =
                              TubeOf.plus_cube disc_tyargs (CubeOf.singleton disc_nf) in
                            let constr_nfs =
                              constr_norm_cube (Modality.src window) constr data_dim tyfam
                                index_vals newvars in
                            CubeOf.miter
                              {
                                it =
                                  (fun _ [ x; c ] ->
                                    let v = is_fresh ctx window seen x in
                                    Hashtbl.add new_vals v c);
                              }
                              [ constr_vars; constr_nfs ];
                            (* Do the rebinding. *)
                            match bind_some (Modality.src window, new_vals) branch_ctx with
                            | Bind_none ->
                                fatal (Matching_wont_refine ("no consistent permutation", None))
                            | Bind_some { checked_perm; oldctx; newctx } -> (
                                (* Everything about the branch is now obtained by the same eval-readback cycle: read back in the old context, where the pattern variables still carry their pre-refinement levels, and re-evaluate in the new one, where the discriminee and the index variables are bound to the values this branch's constructor gives them. *)
                                let new_match_ty =
                                  eval_term (Ctx.env newctx) (readback_val oldctx match_ty) in
                                (* We need that same refined type back in the *old* levels too, since that is where the branch body starts out: the body is evaluated in the environment the match is stuck in, which sends the discriminee to a variable rather than to the constructor, so it is at the old levels but already at the refined type -- that is exactly the sense in which the branch typechecks.  Running the type through the cycle in the other direction gives it: the rebound variables have been substituted away, so all that remains to translate are the pattern variables. *)
                                let old_match_ty =
                                  eval_term (Ctx.env oldctx) (readback_val newctx new_match_ty)
                                in
                                let ebody =
                                  eval
                                    (Permute
                                       (perm, take_args env plus_dim newvars window fw annotate comp))
                                    body in
                                (* The self a branch body is read back against must be refined too, so that a comatch in the body has a self whose spine really does evaluate to it.  Re-evaluating it in the rebound context does that; and since the refinement puts the constructor itself into its spine rather than a variable, running it back through the cycle the other way gives the same refined self at the old levels, which is the one the body starts out at. *)
                                match
                                  eval_term (Ctx.env newctx)
                                    (readback_neu oldctx head_head head_args)
                                with
                                | Neu { head = new_head; args = new_args; _ } -> (
                                    match
                                      eval_term (Ctx.env oldctx)
                                        (readback_neu newctx new_head new_args)
                                    with
                                    | Neu { head = old_head; args = old_args; _ } ->
                                        let old_status =
                                          Potential
                                            (Neu
                                               {
                                                 head = old_head;
                                                 args = old_args;
                                                 value = ready ebody;
                                                 ty = Lazy.from_val old_match_ty;
                                               }) in
                                        (* If the body contains display-only canonical types, this eval of a readback raises an error that we catch below and fall back. *)
                                        let new_ebody =
                                          eval (Ctx.env newctx)
                                            (readback_eval old_status oldctx ebody old_match_ty)
                                        in
                                        let new_status =
                                          Potential
                                            (Neu
                                               {
                                                 head = new_head;
                                                 args = new_args;
                                                 value = ready new_ebody;
                                                 ty = Lazy.from_val new_match_ty;
                                               }) in
                                        (* The branch records the permutation relating the rebound context to the one the pattern variables were added to, exactly as a variable match does when typechecking. *)
                                        Term.Branch
                                          {
                                            annotate = new_annotate;
                                            comp = new_comp;
                                            perm = checked_perm;
                                            tm =
                                              readback_eval new_status newctx new_ebody new_match_ty;
                                          }
                                    | _ ->
                                        fatal (Matching_wont_refine ("rebinding killed self", None))
                                    )
                                | kbody ->
                                    (* This can only happen if glued evaluation is off.  In that case, we can just read back the resulting kinetic value, which is the value of this body. *)
                                    let tm =
                                      Term.Realize (readback_at Kinetic newctx kbody new_match_ty)
                                    in
                                    Term.Branch
                                      {
                                        annotate = new_annotate;
                                        comp = new_comp;
                                        perm = checked_perm;
                                        tm;
                                      }))
                            (* If we can't or won't refine, the remaining approach is to read back the branch using the head, arguments, environment, and a type computed from an explicit motive or from the type of the whole branch. *)
                          ~fatal:(fun d ->
                            match d.message with
                            | Matching_wont_refine _ | Evaluating_display_term _ ->
                                (* The body is evaluated in the environment the match is stuck in, extended by the new pattern variables, exactly as evaluation does it; but that environment still sends the discriminee to a variable rather than to this branch's constructor, so the value and the type are both the unrefined ones. *)
                                let benv =
                                  Permute
                                    (perm, take_args env plus_dim newvars window fw annotate comp)
                                in
                                let ebody = eval benv body in
                                (* The motive is applied to this branch's indices and constructor, in that order, exactly as check_match_branches applies it to compute the type at which to check the branch. *)
                                let branch_ty =
                                  match motive with
                                  | None -> match_ty
                                  | Some mot -> (
                                      (* Slicing the arguments, which live at the total dimension, over the faces of the environment requires the window modality not to have filtered any of the latter away.  If it did, we fall back on the type of the match, the same approximation we use for a match that stores no motive at all. *)
                                      match D.compare (Modality.filtered env_dim fw) env_dim with
                                      | Neq -> match_ty
                                      | Eq ->
                                          let args =
                                            Vec.fold_left
                                              (fun acc c -> acc @ [ val_of_norm_cube c ])
                                              []
                                              (indices_of_out "match branch" out total_dim
                                                 (Vec.length data_indices))
                                            @ [ constr_val_cube constr total_dim newvars ] in
                                          motive_branch_ty window env mot plus_dim match_dim args
                                            benv body) in
                                let bstatus =
                                  Potential
                                    (Neu
                                       {
                                         head = head_head;
                                         args = head_args;
                                         value = ready ebody;
                                         ty = Lazy.from_val branch_ty;
                                       }) in
                                Term.Branch
                                  {
                                    annotate = new_annotate;
                                    comp = new_comp;
                                    perm = id_perm;
                                    tm = readback_eval bstatus branch_ctx ebody branch_ty;
                                  }
                            | _ -> fatal_diagnostic d))
                  branches in
              return
              @@ rewrap
              @@ Term.Match
                   {
                     tm = disc_tm;
                     window;
                     plus_lock = new_plus_lock;
                     dim = total_dim;
                     motive = new_motive;
                     branches = new_branches;
                   }
          | Neq -> fatal (Dimension_mismatch ("readback of stuck match", data_dim, total_dim)))
      | _ -> fatal (Anomaly "discriminee of stuck match is not of a datatype with all its indices"))
  | Potential _, Match _ -> fatal (Anomaly "stuck match is not a neutral")
  | _ -> no_display "a stuck metavariable"

(* The "about" command reads back the *potential* value of a neutral, passing the neutral itself as readback's status so that a canonical type displays as its declaration and a comatch as itself; readback_at handles the rest, including descending through parameter abstractions.  None means the neutral has no potential value at all to display -- an axiom, or a permanently stuck case tree -- so the caller shows its normal form instead. *)
let rec readback_about : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) Value.value -> (mode, b, potential) Term.term option =
 fun ctx value ->
  match value with
  | Neu { value = v; ty; _ } -> (
      match force_eval v with
      | Val v -> Some (readback_at (Potential value) ctx v (Lazy.force ty))
      (* A neutral whose case tree got stuck on a match displays as that match. *)
      | Unrealized (Some pn) -> readback_stuck (Potential value) ctx pn (Lazy.force ty)
      (* Under glued evaluation, a constant whose definition is an ordinary term rather than a case tree is a neutral whose value realizes that term.  It has no potential value of its own, but the neutral it realizes to may, so we look there. *)
      | Realize v -> readback_about ctx v
      | Unrealized None -> None)
  | _ -> None
