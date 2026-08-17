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

(* The level of a value that is a bare free variable with no degeneracy applied, which is the case in which a match's discriminee can be rebound to refine a branch. *)
let level_of_free_var : type mode dom mu.
    (dom, mu, mode) Modality.t -> (dom, kinetic) value -> level option =
 fun mu v ->
  match view_term v with
  | Neu { head = Var { level; deg; key }; args = Emp; _ } -> (
      (* Unkeyed means an identity 2-cell on the variable's own annotation, which for a discriminee is the match's window. *)
      match (is_id_deg deg, Modalcell.compare key (Modalcell.id mu)) with
      | Some _, Eq -> Some level
      | _ -> None)
  | _ -> None

(* A stuck spine taken apart: the context the match at its head end must be displayed in -- ours, locked by the left adjoint of every field projection the spine crosses -- together with the function that puts the spine back around a term displayed there.  This is the walk readback_neu makes over a neutral's spine, but starting from a term rather than a head and at whatever energy that term has, which is what App, Inst, Act and Field are energy-polymorphic for. *)
type (_, _, _) stuck_spine =
  | Stuck_spine :
      ('hmode, 'z, 'c) Ctx.t * (('hmode, 'c, potential) term -> ('mode, 'a, potential) term)
      -> ('hmode, 'mode, 'a) stuck_spine

(* Rebind a variable of an environment, identified by its level, to a given value.  This is a partial dual of lookup: a lookup accumulates the operator actions, shifts and keys it passes on the way in and applies them to the value it finds on the way out, and those actions cannot in general be undone in order to push a *new* value back in.  So we look only through the forms that arise in the environment of a case tree -- extensions and permutations -- and return None otherwise, leaving the caller to fall back.  We check the cheap conditions on an entry before forcing its value to see whether it is the variable we want, since a lambda stores its argument lazily; this runs only on the display path, and only once an unrefined readback has already failed. *)
let rec rebind_level : type mode vdom vmod vk n b.
    (mode, n, b) env ->
    (vdom, vmod, mode) Modality.t ->
    level ->
    (vk, (vdom, kinetic) value) CubeOf.t ->
    (mode, n, b) env option =
 fun env mu lvl v ->
  match env with
  | Ext { env; plus; filter; filtered; values } -> (
      let unchanged () =
        Option.map
          (fun env -> Ext { env; plus; filter; filtered; values })
          (rebind_level env mu lvl v) in
      (* The entry must be annotated by the modality the new value lives at -- which for a match's discriminee is its window -- and be a cube of the same dimension, so that the new values fit where the old ones were.  At a positive dimension that means rebinding the whole cube, boundary faces and all, which is right: in the branch the entire cube is the constructor's. *)
      match
        ( Modality.compare (Modality.filter_modality filter) mu,
          D.compare (D.plus_out (Modality.filtered (dim_env env) filter) plus) (CubeOf.dim v) )
      with
      | Eq, Eq -> (
          let entry =
            match values with
            | `Ok cube -> Some (CubeOf.find_top cube)
            | `Lazy cube -> Some (force_eval_term (CubeOf.find_top cube))
            | `Error _ -> None in
          match entry with
          | Some (Neu { head = Var { level; deg; key }; args = Emp; _ })
            when level = lvl
                 && Option.is_some (is_id_deg deg)
                 &&
                 match Modalcell.compare key (Modalcell.id mu) with
                 | Eq -> true
                 | Neq -> false -> Some (Ext { env; plus; filter; filtered; values = `Ok v })
          | _ -> unchanged ())
      | _ -> unchanged ())
  | Permute (p, env) -> Option.map (fun env -> Permute (p, env)) (rebind_level env mu lvl v)
  | _ -> None

(* Rebind, in both the environment the match is stuck in and the environment of the readback context, the discriminee and any of the datatype's index variables that are themselves free variables, to the values they take in a given branch.  Applying the *same* rebindings to both is what keeps the branch body and the type it is read back at in step: the body evaluates to what it was checked to be, and the type refines with it.  A rebinding that either environment can't take is dropped from both, leaving that variable unrefined in both.  The discriminee's own rebinding is required, so None if that one fails. *)
let rebind_branch : type mode dom window z a n b k.
    (mode, z, a) Ctx.t ->
    (mode, n, b) env ->
    (dom, window, mode) Modality.t ->
    (level * (k, (dom, kinetic) value) CubeOf.t) list ->
    level * (k, (dom, kinetic) value) CubeOf.t ->
    ((mode, n, b) env * (mode, D.zero, a) env) option =
 fun ctx env window indices (disc_level, disc_val) ->
  (* The values we bind live at the discriminee's mode, which the window maps to the mode the environments live at; rebind_level checks each entry's annotation against it. *)
  match
    ( rebind_level env window disc_level disc_val,
      rebind_level (Ctx.env ctx) window disc_level disc_val )
  with
  | Some env, Some ctxenv ->
      Some
        (List.fold_left
           (fun (env, ctxenv) (lvl, v) ->
             match (rebind_level env window lvl v, rebind_level ctxenv window lvl v) with
             | Some env, Some ctxenv -> (env, ctxenv)
             | _ -> (env, ctxenv))
           (env, ctxenv) indices)
  | _ -> None

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
  match (vty, view, status) with
  (* For potential values, we read back comatches, tuples, and canonical types against the neutral the status carries, which serves as their self-variable.  By contrast, matches never occur as values directly: instead they are stuck heads of evaluations (the Unrealized case of readback_eval). *)
  | _, Struct _, Potential neutral -> (
      match readback_comatch ctx neutral ty with
      | Some res -> res
      (* A comatch with a genuinely stuck instance retains no trace of what it is stuck on, so we fall back to the neutral's application spine. *)
      | None -> Realize (readback_val ctx neutral))
  | ( Canonical
        (type hmode m n mn)
        ((_, UU (_, mk), ins0, boundary) :
          (hmode, kinetic) head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      Canonical { canonical; ins; tyargs; _ },
      Potential neutral ) -> (
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
  (* Abstractions (kinetic or potential) are read back uniformly by extending the context using their pi-type. *)
  | Canonical (_, Pi { x = _; filter; doms; cods }, ins, tyargs), Lam (x, filter2, body), _ -> (
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
  | Canonical (_, Pi { x = name; filter; doms; cods }, ins, tyargs), tm, _ when eta ->
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
  (* Similarly at an eta-expanding record type, but controlled by the type's eta and opacity rather than the eta argument passed to readback_at. *)
  | ( Canonical
        (type hmode mn m n)
        (( _,
           Codata
             (type a et)
             ({ eta; opacity; fields; env = _; hints = _ } : (mode, m, n, a, et) codata_args),
           ins,
           _ ) :
          (hmode, kinetic) head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      _,
      _ ) -> (
      match eta with
      (* A no-eta codatatype: an ordinary readback of a (kinetic) neutral here yields its application spine.  Displaying a comatch as a comatch is done by readback_comatch, which forces the neutral's potential value; that was caught earlier by the Struct/Potential case. *)
      | Noeta -> readback_val_sorted ctx tm vty
      | Eta -> (
          (* An eta-record type.  Only kinetic values are ever read back here (records, and tuples reached via their neutral); a tuple in a case tree (a potential eta-struct) is never passed to readback for display. *)
          let dim = cod_left_ins ins in
          let fldins = ins_zero dim in
          let readback_at_record (tm : (mode, kinetic) value) ty =
            match (tm, opacity) with
            (* If the term is a struct, we read back its fields.  Even though this is not technically an eta-expansion, we have to do it here rather than in readback_val because we need the record type to determine the types at which to read back the fields. *)
            | Struct { fields = tmflds; energy; ins = _; eta = _ }, _ ->
                let fields =
                  Mbwd.map
                    (* We don't need to consider the Higher case since we are kinetic. *)
                    (fun (Value.StructfieldAbwd.Entry
                            (fld, Value.Structfield.Lower (adj, fldtm, lbl))) ->
                      (* The component of a modal field lives behind a lock by the right adjoint, so we read it back in the locked context, at the non-keyed component type. *)
                      let (Tyof_modal_field (adj', ety)) = tyof_field_nokey (Ok tm) ty fld in
                      match Modality.compare (Modalcell.adj_left adj') (Modalcell.adj_left adj) with
                      | Neq -> fatal (Anomaly "adjunction mismatch in struct readback")
                      | Eq ->
                          let (Locked (plus_lock, lctx)) = Ctx.lock ctx (Modalcell.adj_right adj') in
                          Term.StructfieldAbwd.Entry
                            ( fld,
                              Term.Structfield.Lower
                                ( adj',
                                  plus_lock,
                                  readback_at Kinetic lctx (force_eval_term fldtm) ety,
                                  lbl ) ))
                    tmflds in
                Some (Term.Struct { eta = Eta; dim; fields; energy })
            (* In addition, if the record type is transparent, or if it's translucent and the term is a tuple in a case tree, and we are reading back for display (rather than for internal typechecking purposes), we do an eta-expanding readback. *)
            | (_, `Transparent l | _, `Translucent l)
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
                let m = cod_left_ins ins in
                let fields =
                  Bwd.filter
                    (fun (CodatafieldAbwd.Entry
                            (type i)
                            ((_, Codatafield (Adjunction { left; _ }, _, _)) :
                              i Field.t * (i, mode * a * D.zero * n * has_eta) Codatafield.t)) ->
                      let (Has_filter left_filter) = Modality.filter left m in
                      match Modality.filter_is_trivial m left_filter with
                      | Some Eq -> true
                      | None -> false)
                    fields in
                let fields =
                  Mbwd.map
                    (fun (CodatafieldAbwd.Entry
                            (type i)
                            (( fld,
                               Codatafield ((Adjunction { left; right; unit; _ } as adj), _, Lower _)
                             ) :
                              i Field.t * (i, mode * a * D.zero * n * has_eta) Codatafield.t)) ->
                      (* Eta-expansion of a modal field: key the term by the adjunction unit, project, and read back the component in the context locked by the right adjoint (as in the eta-rule for equality). *)
                      let xu = act_value tm (id_deg D.zero) unit in
                      let tyu = act_ty tm ty (id_deg D.zero) unit in
                      let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                      Term.StructfieldAbwd.Entry
                        ( fld,
                          Term.Structfield.Lower
                            ( adj,
                              plus_lock,
                              readback_at Kinetic lctx (field_term left xu fld fldins)
                                (tyof_field left (Ok xu) tyu fld fldins),
                              l ) ))
                    fields in
                Some (Struct { eta = Eta; dim; fields; energy = Kinetic })
            (* If the term is not a struct and the record type is not transparent/translucent, we pass off to synthesizing readback. *)
            | _ -> None in
          let do_record (rtm : (mode, kinetic) value) =
            match is_id_ins ins with
            | Some _ -> (
                match readback_at_record rtm ty with
                | Some res -> res
                | None -> readback_val_sorted ctx rtm vty)
            | None -> (
                (* A nontrivially permuted record is not a record type, but we can permute its arguments to find elements of a record type that we can then eta-expand and re-permute. *)
                let (Perm_to p) = perm_of_ins ins in
                let pinv = deg_of_perm (perm_inv p) in
                let ptm = act_value rtm pinv (Modalcell.id2 (Ctx.mode ctx)) in
                let pty = act_ty rtm ty pinv (Modalcell.id2 (Ctx.mode ctx)) in
                match readback_at_record ptm pty with
                | Some res -> Act (Kinetic, res, deg_of_perm p, (`Other, `Other))
                | None -> readback_val_sorted ctx rtm vty) in
          match view with
          | Struct { energy = Kinetic; _ } -> do_record view
          | Neu _ -> do_record view
          | _ -> readback_val_sorted ctx tm vty))
  (* Datatypes are not eta-expanding, but we still need the datatype in order to read back a constructor at that type. *)
  | Canonical (_, Data { constrs; _ }, ins, tyargs), Constr (xconstr, xn, xargs), _ -> (
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
  | _ -> readback_val_sorted ctx tm vty

and readback_val_sorted : type mode a z s.
    (mode, z, a) Ctx.t -> (mode, s) value -> mode View.view_type -> (mode, a, s) term =
 fun ctx tm vty ->
  let sort = sort_of_ty ctx vty in
  readback_val ~sort ctx tm

(* The synthesizing readback only ever applies to neutrals (a kinetic value).  Any other value reaching it (which can only be a potential value, since other callers pass kinetic neutrals) is an anomaly. *)
and readback_val : type mode a z s.
    ?sort:[ `Type | `Function | `Other ] ->
    (mode, z, a) Ctx.t ->
    (mode, s) value ->
    (mode, a, s) term =
 fun ?(sort = `Other) ctx x ->
  match x with
  | Neu { head; args; value; ty } -> (
      match (force_eval value, Displaying.read ()) with
      | Realize v, true -> readback_at Kinetic ctx v (Lazy.force ty)
      | Val (Canonical _), _ -> readback_neu ~sort:(sort, `Canonical) ctx head args
      | _ -> readback_neu ~sort:(sort, `Other) ctx head args)
  | Lam _ -> fatal (Readback_at_wrong_type "a lambda, which does not synthesize")
  | Struct _ -> fatal (Readback_at_wrong_type "a struct, which does not synthesize")
  | Constr _ -> fatal (Readback_at_wrong_type "a constructor, which does not synthesize")
  | Canonical _ -> fatal (Readback_at_wrong_type "a canonical type, which does not synthesize")

and readback_neu : type hmode mode a z any.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (mode, z, a) Ctx.t ->
    (hmode, kinetic) head ->
    (hmode, mode, any) apps ->
    (mode, a, kinetic) term =
 fun ?(sort = (`Other, `Other)) ctx head apps ->
  match (apps, head) with
  | Emp, _ -> readback_head ~sort ctx head
  | Arg (apps, filter, args, ins), _ ->
      let modality = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      let (Locked (plus, lctx)) = Ctx.lock ctx modality in
      Term.Act
        ( Kinetic,
          App
            ( Kinetic,
              readback_neu ~sort ctx head apps,
              cod_left_ins ins,
              filter,
              Modal
                ( modality,
                  plus,
                  CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf lctx tm) } [ args ] ) ),
          p,
          sort )
  | Field (apps, filter, fld, fldplus, ins), _ -> (
      let fm = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      (* The spine inside a modal field projection lives behind a lock by the left adjoint, so we read it back in the locked context, at the filtered dimension. *)
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx fm in
      let t = cod_left_ins ins in
      let inner = readback_neu ~sort lctx head apps in
      match Modality.filter_is_trivial t filter with
      | Some Eq ->
          (* Trivial filter: the inner spine is at the full result dimension t, and we build the projection there directly. *)
          Term.Act
            (Kinetic, Field (Kinetic, Modal (fm, plus_lock, inner), fld, id_ins t fldplus), p, sort)
      | None ->
          (* Nontrivial filter: the field's modality is nonparametric and a degeneracy has acted, so the inner spine lives at a strictly smaller filtered dimension ft than the result dimension t.  We read back the projection at ft and lift it to t by the filter's degeneracy, which reconstructs (and prints as) the acting degeneracy — this is exactly the "disappeared" projection viewed as a degeneracy of a lower-dimensional one, and it re-evaluates correctly since eval filters the environment dimension. *)
          let ft = Modality.filtered t filter in
          let (Plus new_fldplus) = D.plus (D.plus_right fldplus) in
          let fieldterm : (_, _, kinetic) Term.term =
            Term.Field (Kinetic, Modal (fm, plus_lock, inner), fld, id_ins ft new_fldplus) in
          let liftdeg = Modality.deg_of_filter t filter in
          Term.Act (Kinetic, Term.Act (Kinetic, fieldterm, liftdeg, sort), p, sort))
  | Inst (Emp, _, args), Pi _ when TubeOf.is_full args ->
      (* When reading back a fully instantiated higher-dimensional pi-type, we eta-expand the instantiation arguments so that it can be printed with a nice notation. *)
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ~eta:true ctx x) } [ args ] in
      Inst (Kinetic, readback_head ~sort ctx head, args)
  | Inst (apps, _, args), _ ->
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ args ] in
      Inst (Kinetic, readback_neu ~sort ctx head apps, args)

and readback_head : type mode c z.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (mode, z, c) Ctx.t ->
    (mode, kinetic) head ->
    (mode, c, kinetic) term =
 fun ?(sort = (`Other, `Other)) ctx h ->
  match h with
  | Var { level; deg; key } -> (
      (* The source of the key is supposed to be the modal annotation of the variable, while its target is supposed to be the composite of all the locks in the context to its right (including any added by the degeneracy).  So we remove its target from the context. *)
      let (Remove_lock (ctx, plus_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt key) in
      (* Now we look for the level variable in the remaining context. *)
      let (Lookup
             {
               result;
               value = _;
               dirt = _;
               modality;
               filter;
               insert;
               plus = Plus_with_locks (c, _);
             }) =
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
            | None -> Act (Kinetic, Term.Var (Index (insert, fa, filter, iplus)), deg, sort) in
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
      | None -> Act (Kinetic, Const name, deg, sort))
  | Meta { meta; env; ins } -> (
      let tm = MetaEnv (meta, readback_env ctx env (Global.find_meta meta).termctx) in
      match is_id_ins ins with
      | Some _ -> tm
      | None ->
          let (To perm) = deg_of_ins ins in
          Act (Kinetic, tm, perm, sort))
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
    Cod (kfilter, readback_val ~sort:`Type sctx (apply_binder_term b kfilter sargs)) in
  Term.Pi
    {
      x;
      filter;
      doms =
        Modal
          ( modality,
            plus,
            CubeOf.mmap { map = (fun _ [ dom ] -> readback_val ~sort:`Type lctx dom) } [ doms ] );
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
              ({ tm = None; ty = readback_val ~sort:`Type ctx (Lazy.force (Binding.value b).ty) }
                : (mode, b) binding)
          | None ->
              {
                tm = Some (readback_nf ctx (Binding.value b));
                ty = readback_val ~sort:`Type ctx (Lazy.force (Binding.value b).ty);
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
                  readback_val ~sort:`Type lctx
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
    Canonical (Data { indices = ij; constrs; discrete; recursive; tyfam; hints }) in
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
  readback_val ~sort:`Type ctx (Norm.inst ft boundary)

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
     (Term.CodatafieldAbwd.Entry
        (type i)
        ((fld, Codatafield ((Adjunction { left; right; unit; _ } as adj), fld_plus_lock, cf)) :
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
             let ty = readback_val ~sort:`Type sctx ety in
             Term.CodatafieldAbwd.Entry (fld, Codatafield (adj, plus_lock, Lower ty))
         | Higher (fldtermctx, fldtys) -> (
             (* A codatatype with a higher field has intrinsic dimension zero, so its whole dimension, at which the self-variable cube lives and at which the instances of the field are indexed, is its evaluation dimension. *)
             match D.compare evaldim (CubeOf.dim selfnfs) with
             | Neq ->
                 fatal (Anomaly "higher field of a codatatype with positive intrinsic dimension")
             | Eq ->
                 let tys =
                   readback_higher_codatafield ctx codataenv fld_plus_lock fldtermctx fldtys
                     (CubeOf.dim selfnfs) fld adj selfnfs sctx in
                 (* The context that the displayed field's types are evaluated over is also stored, as it is for a declared higher field, so that it could be degenerated further. *)
                 Term.CodatafieldAbwd.Entry
                   (fld, Codatafield (adj, plus_lock, Higher (readback_ctx lctx, tys)))))

(* Read back the instances of one higher field of a codatatype value being displayed, as the pbijmap of types that Codatafield.Higher stores: one entry per partial bijection between the codatatype's dimension m and the field's intrinsic dimension.  The self variable, its cube, and the context they live in are those built by readback_codata, while the environment, lock, termctx and stored types are those of the codatatype value being displayed; the ambient context is needed only to degenerate for a non-projectable instance. *)
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
          (pbij : (m, i, r) pbij)
          :
          (r, gmode * (bg, (f, m) dim_entry) snoc) Term.FieldtypeFam.t
        ->
          let (Pbij (fldins, fldshuf)) = pbij in
          match D.compare_zero (left_shuffle fldshuf) with
          | Zero ->
              (* Projectable instance: read back in the locked, self-extended context, as for a lower field, with a trivial degeneration and hence no remaining dimensions for the self cube to be degenerated by.  As there, we display the type as it was *declared*, computed from the codatatype's own environment and left un-keyed (~key:`Nokey). *)
              let Eq = eq_of_zero_shuffle fldshuf in
              let ety =
                tyof_higher_codatafield
                  (`Ok (val_of_norm_cube selfnfs))
                  (TubeOf.boundary selfnfs) (D.zero_plus m) fld adj codataenv fldins ~shuf:Trivial
                  plus_lock fldtermctx ic0 fldty ~key:`Nokey in
              Fieldtype (Plusmap.zerol (Ctx.tctx sctx), readback_val ~sort:`Type sctx ety)
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
              Fieldtype (plusmap, readback_val ~sort:`Type dsctx ety));
    }

(* Read back a codatatype value whose insertion is *not* the identity, i.e. one to which a nontrivial permutation of its dimensions has been applied.  Such a value is no longer a record type at all: its fields can't be projected, and there is no self-variable cube in the order in which the fields were declared.  But it is the permutation of a value that is one, so we un-permute it, read that back as a codatatype, and apply the permutation to the result as a degeneracy.

   That works directly only when the codatatype is uninstantiated, for then it is a higher-dimensional *term* of a universe, whose dimensions a degeneracy acts on. An instantiated one we first un-instantiate entirely (uninstantiate), permute as the uninstantiated codatatype it then is, and re-instantiate, the way readback_data displays an instantiated datatype.

   Both halves of that are necessary.  A *partially* instantiated codatatype, such as "(Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,)", has no un-permuted form at all, since a permutation generally mixes its instantiated and uninstantiated dimensions while an instantiation tube instantiates the *last* dimensions.  And although a *fully* instantiated one can be un-permuted where it stands, by a symmetry permuting its instantiation arguments, displaying it that way would be wrong: readback_codata absorbs the instantiation arguments into the self variable, so its result reads as a record type of the lower dimension -- "sig ( ungel : Id R a₂ b₂ r₀ r₁ )" -- which denotes nothing that the permutation could be applied to.  Un-instantiating puts the arguments back outside, where the permutation has a higher-dimensional codatatype to act on.

   Since this is display-only, anything unexpected along the way -- an un-permuted value that is somehow still permuted, or an un-instantiation that doesn't produce the type we expect -- falls back on the application spine of the neutral rather than failing. *)
and readback_permuted_codata : type mode a b m k mk e n.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (m, k, mk, mode normal) TubeOf.t ->
    (mk, e, n) insertion ->
    (mode, b, potential) term =
 fun ctx neutral tyargs ins ->
  let mode = Ctx.mode ctx in
  let spine () : (mode, b, potential) term = Realize (readback_val ctx neutral) in
  (* Un-instantiating rebuilds a type, and so can report a bug if the value is not shaped as it expects.  As this is display-only, we catch that, along with our own failures below, and show the spine instead.  The guard has to cover the whole function rather than just the call: the rebuilt type is lazy, and is not forced until the recursive call acts on it. *)
  Reporter.try_with ~fatal:(fun _ -> spine ()) @@ fun () ->
  match D.compare_zero (TubeOf.inst tyargs) with
  (* Instantiated, wholly or partly: un-instantiate, permute that, and re-instantiate.  The insertion is unchanged by instantiation, so it is still the one to un-permute by, now at a value whose instantiation is empty; hence the recursive call lands in the uninstantiated case below. *)
  | Pos _ ->
      let uninst = uninstantiate mode neutral in
      Inst
        ( Potential,
          readback_permuted_codata ctx uninst.tm (TubeOf.empty (TubeOf.out tyargs)) ins,
          TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ tyargs ] )
  | Zero -> (
      let (Perm_to p) = perm_of_ins ins in
      let pinv = deg_of_perm (perm_inv p) in
      let cell = Modalcell.id2 mode in
      match act_value neutral pinv cell with
      | Neu { value; ty = pty; _ } as pneutral -> (
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
              | _ -> spine ())
          | _ -> spine ())
      | _ -> spine ())

(* Un-instantiate a type value: strip the instantiation off the end of its neutral spine, and off its canonical value, returning the whole-dimensional type that was instantiated, as a normal.  A value carrying no instantiation is returned unchanged, which is what bottoms out the recursion below.

   The uninstantiated type's own type is not stored anywhere -- inst computes the instantiated type from it and keeps only the spine -- so we rebuild it: a universe of the whole dimension, instantiated at the uninstantiated type's boundary.  That boundary is exactly what we are stripping off, in the two halves that a full tube splits into: its outer part is the *types* of the instantiation arguments, and its inner part (empty unless the instantiation was partial) is the arguments of the universe that the instantiated type itself belongs to.  Both arrive instantiated in their turn -- what we have of the boundary of "(Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,)" is "Gel A B R a₀ b₀" and "Id A a₀ a₁", where we want "Gel A B R" and "Id A" -- so we un-instantiate them recursively.  The recursion is on dimension, since each of them is lower-dimensional than the whole. *)
and uninstantiate : type mode. mode Mode.t -> (mode, kinetic) value -> mode normal =
 fun mode ty ->
  match view_term ty with
  | Neu { head; args = Inst (base_args, _, insargs); value; ty = instty } -> (
      match view_type (Lazy.force instty) "uninstantiate" with
      | Canonical (_, UU (_, umk), uins, uargs) -> (
          let Eq = eq_of_ins_zero uins in
          (* The universe the instantiated type belongs to has exactly its uninstantiated dimensions. *)
          match D.compare umk (TubeOf.uninst insargs) with
          | Neq -> fatal (Anomaly "uninstantiating a type not in its own universe")
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

(* ********** Readback of stuck matches (for display only) ********** *)

(* Read back a stuck case tree: check_match_branches run backwards.  For each constructor we invent fresh pattern variables from its stored function-type, with ext_pi, exactly as typechecking does; extend the stored environment by them, with take_args, exactly as evaluation does; evaluate the branch body there; and read it back in the context extended by the same variables.  The reconstructed branch carries ext_pi's own annotate and comp -- which name the pattern variables after the constructor's arguments -- and the identity permutation, rather than the stored ones, which are relative to the original checking context.

   We reconstruct only when the stuck spine is empty, which is exactly when the type we were handed is the type of the match itself rather than of something the match was applied to; with a nonempty spine there would be no type at which to read back the branch bodies.  We also reconstruct only a match: a stuck metavariable has no branches to show.  In every other case we return None and the caller falls back to the application spine.

   The pattern variables are *not* substituted into the type or the context, so for a match that refines its motive the branch bodies are read back at the unrefined type rather than at the refined one that typechecking used.  The two are definitionally equal in the branch, so where the unrefined type still exposes the canonical form that readback needs -- which is everything except a motive that is itself a stuck match -- the display is right.  Where it doesn't, readback raises, and we catch that and fall back to the application spine, exactly as if there had been no payload at all.  Note this is display-only output, like the readback of a canonical type: it is never re-typechecked or re-evaluated. *)
and readback_stuck : type mode a z hmode any.
    (mode, potential) readback_status ->
    (mode, z, a) Ctx.t ->
    (hmode, potential) head * (hmode, mode, any) apps ->
    (mode, kinetic) value ->
    (mode, a, potential) term option =
 fun status ctx pn ty ->
  (* Reading a branch body back can legitimately fail, because the type we read it at only approximates the type it was checked at; that is Readback_at_wrong_type, which we catch and turn into the fallback.  Everything else, including the anomalies below that state invariants which should hold, is a real bug and passes through as one rather than being absorbed silently. *)
  Reporter.try_with ~fatal:(fun d ->
      match d.message with
      (* The one thing that can legitimately go wrong here: the type we read a branch body back at only approximates the type it was checked at, so the body may not fit it.  Anything else is a real bug and is passed through as one. *)
      | Readback_at_wrong_type str ->
          no_display (Printf.sprintf "a stuck match with a branch body that is %s" str)
      | _ -> fatal_diagnostic d)
  @@ fun () -> readback_stuck_match status ctx pn ty

(* Read back the term that justified refuting a branch, given an environment for the branch's context: evaluate it through its own window modality, exactly as evaluation evaluates a match's discriminee, and read the result back in the context locked by that modality.  The result carries the same data a match takes for its discriminee, which is what a refutation displays as. *)
and stuck_spine : type hmode mode a z any.
    (mode, z, a) Ctx.t -> (hmode, mode, any) apps -> (hmode, mode, a) stuck_spine =
 fun ctx -> function
  | Emp -> Stuck_spine (ctx, fun tm -> tm)
  | Arg (rest, filter, args, ins) ->
      let modality = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      let (Locked (plus, lctx)) = Ctx.lock ctx modality in
      let (Stuck_spine (hctx, rewrap)) = stuck_spine ctx rest in
      Stuck_spine
        ( hctx,
          fun tm ->
            Term.Act
              ( Potential,
                App
                  ( Potential,
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
      let (Stuck_spine (hctx, rewrap)) = stuck_spine ctx rest in
      Stuck_spine
        ( hctx,
          fun tm ->
            Inst
              ( Potential,
                rewrap tm,
                TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ args ] ) )
  (* A field projection crosses to the mode the field's left adjoint comes from, so the rest of the spine, and the match at its end, live in our context locked by it. *)
  | Field (rest, filter, fld, fldplus, ins) -> (
      let fm = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx fm in
      let t = cod_left_ins ins in
      let (Stuck_spine (hctx, rewrap)) = stuck_spine lctx rest in
      match Modality.filter_is_trivial t filter with
      | Some Eq ->
          Stuck_spine
            ( hctx,
              fun tm ->
                Term.Act
                  ( Potential,
                    Field (Potential, Modal (fm, plus_lock, rewrap tm), fld, id_ins t fldplus),
                    p,
                    (`Other, `Other) ) )
      | None ->
          (* As in readback_neu: a nonparametric field at a dimension its modality filters is read back at the filtered dimension and lifted by the filter's degeneracy. *)
          let ft = Modality.filtered t filter in
          let (Plus new_fldplus) = D.plus (D.plus_right fldplus) in
          let liftdeg = Modality.deg_of_filter t filter in
          Stuck_spine
            ( hctx,
              fun tm ->
                Term.Act
                  ( Potential,
                    Term.Act
                      ( Potential,
                        Field
                          (Potential, Modal (fm, plus_lock, rewrap tm), fld, id_ins ft new_fldplus),
                        liftdeg,
                        (`Other, `Other) ),
                    p,
                    (`Other, `Other) ) ))

and readback_stuck_match : type mode a z hmode any.
    (mode, potential) readback_status ->
    (mode, z, a) Ctx.t ->
    (hmode, potential) head * (hmode, mode, any) apps ->
    (mode, kinetic) value ->
    (mode, a, potential) term option =
 fun status ctx (Stuck { env; tm = ctm; ins }, apps) ty ->
  match ctm with
  | Match { tm; window; plus_lock; dim = match_dim; motive; branches } -> (
      (* The match at the head end of the spine is displayed in our context locked by the field projections the spine crosses, and the spine is put back around it afterwards. *)
      let (Stuck_spine (ctx, rewrap)) = stuck_spine ctx apps in
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
      match disc with
      | Lam _ | Struct _ | Constr _ ->
          fatal (Anomaly "discriminee of a stuck match is not a neutral")
      | Neu { ty = (lazy discty); _ } -> (
          match view_type discty "readback_stuck" with
          | Canonical
              (_, Data { dim = data_dim; constrs; indices = data_indices; _ }, disc_ins, disc_tyargs)
            -> (
              (* The dimension of the datatype the discriminee actually evaluated to must be the total dimension: the stored match dimension plus the dimension of the environment we are stuck in.  Evaluation checks the same thing of the constructor it reduces with, and likewise treats a mismatch as an error rather than a reason to give up. *)
              match D.compare data_dim total_dim with
              | Neq -> fatal (Dimension_mismatch ("readback of stuck match", data_dim, total_dim))
              | Eq -> (
                  (* A datatype has intrinsic dimension zero, so its instantiation tube is at its substitution dimension. *)
                  let Eq = eq_of_ins_zero disc_ins in
                  let (Locked (new_plus_lock, lctx)) = Ctx.lock ctx window in
                  let disc_tm = readback_val lctx disc in
                  (* The self a branch body is read back against must live at the mode of the match, not of the whole spine, so we take the neutral we were given and strip the spine's eliminations back off it. *)
                  let (Potential outer_neutral) = status in
                  match outer_neutral with
                  | Neu { head = head_head; args; _ } -> (
                      match strip_apps args apps with
                      | Some (Any head_args) -> (
                          (* An explicit motive is a type family over the datatype's indices and the datatype itself; evaluated in the environment we are stuck in, it gives the type of each branch when applied to that branch's indices and constructor.  A non-dependent match instead records one type, which is that of the match and of every branch alike. *)
                          let emotive =
                            match motive with
                            | Some (`Family t) -> Some (eval_term env t)
                            | Some (`Type _) | None -> None in
                          let stored_ty =
                            match motive with
                            | Some (`Type t) -> Some (eval_term env t)
                            | Some (`Family _) | None -> None in
                          (* The type we were handed is the type of the whole stuck spine, which is the match's own type only when the spine is empty.  Otherwise we need the motive, which gives it as check_match_branches computes the type of the match itself: applied to the discriminee's indices, then its instantiation arguments, then the discriminee. *)
                          let motive_ty =
                            match (emotive, data_indices) with
                            | Some emotive, Filled var_indices ->
                                let r =
                                  Vec.fold_left (apply_singleton_nfs window) emotive var_indices
                                in
                                let r = apply_singleton_tube_nfs window r disc_tyargs in
                                Some
                                  (apply_term r (Modality.filter_zero window)
                                     (CubeOf.singleton disc))
                            | _ -> None in
                          let match_ty =
                            match (motive_ty, stored_ty, empty_apps apps) with
                            | Some t, _, _ -> Some t
                            | None, Some t, _ -> Some t
                            | None, None, Some Eq -> Some ty
                            | None, None, None -> None in
                          match match_ty with
                          | None ->
                              no_display
                                "a stuck match applied to further arguments, with no motive to give the type of the match itself"
                          | Some match_ty ->
                              let new_branches =
                                Constr.Map.mapi
                                  (fun constr br ->
                                    match br with
                                    | Term.Branch { annotate; comp; perm; tm = body } ->
                                        let (Dataconstr { env = cenv; ty = cty }) =
                                          Abwd.find_opt constr constrs
                                          <|> Anomaly
                                                "constructor missing from stuck match in readback"
                                        in
                                        (* Fresh pattern variables, named as the user named them in the branch (that is what the stored annotations carry the names for); ext_pi fills in the constructor's own argument name for any that were anonymous. *)
                                        let (Wrap arity) = pi_arity cty in
                                        let (Bplus plus_args) = Raw.Indexed.bplus arity in
                                        let xs =
                                          match
                                            Vec.of_list_length arity (annotate_names annotate)
                                          with
                                          | Some names -> Raw.Indexed.Namevec.of_vec plus_args names
                                          | None ->
                                              fatal (Anomaly "constructor argument length mismatch")
                                        in
                                        let (Ext_pi
                                               {
                                                 ctx = newctx;
                                                 values = newvars;
                                                 annotate = new_annotate;
                                                 comp = new_comp;
                                                 out;
                                                 normals = _;
                                               }) =
                                          ext_pi ctx window cenv xs (Norm.eval_term cenv cty) in
                                        (* The type at which to read this branch back, computed from the motive exactly as check_match_branches computes the type at which to check it: apply the motive to this branch's indices, read off the constructor's residual output type, and then to the constructor itself with its boundary. *)
                                        let branch_ty =
                                          match (emotive, data_indices) with
                                          | None, _ -> match_ty
                                          | Some _, Unfilled _ ->
                                              fatal
                                                (Anomaly
                                                   "unsaturated datatype in stuck match readback")
                                          | Some emotive, Filled var_indices ->
                                              apply_singletons window
                                                (Vec.fold_left (apply_singleton_nfs window) emotive
                                                   (indices_of_out "match branch" out total_dim
                                                      (Vec.length var_indices)))
                                                (constr_cube constr total_dim newvars) in
                                        (* The body is evaluated with the *stored* annotate/comp/perm, which are the ones that match the stored environment and the body's own context. *)
                                        let branch bhead bargs bodyenv branch_ty =
                                          let bodyev = eval (Permute (perm, bodyenv)) body in
                                          (* A branch body that is a comatch, a tuple, or a canonical type is read back against a "self": readback_comatch and readback_codata want a neutral whose forced value is the very struct they are displaying, since they compute the field types against it and project the components out of it.  The enclosing neutral is that, under this branch's hypothesis -- so we hand them it with this branch's value and type in place of the stuck match's.  This is why such a body no longer has to be given up on, and it needs no refinement, so it works for a non-variable discriminee too.  The self never reaches the output: readback_codata binds a fresh self variable, readback_data takes its constructors' output types from the stored tyfam, and a projection out of the self reduces to the component the comatch stores. *)
                                          let bstatus =
                                            Potential
                                              (Neu
                                                 {
                                                   head = bhead;
                                                   args = bargs;
                                                   value = ready bodyev;
                                                   ty = lazy branch_ty;
                                                 }) in
                                          Term.Branch
                                            {
                                              annotate = new_annotate;
                                              comp = new_comp;
                                              perm = id_perm;
                                              tm = readback_eval bstatus newctx bodyev branch_ty;
                                            } in
                                        (* A variable match refines the context rather than applying a motive, so neither the type we were handed nor any stored motive is the type its branches were checked at.  What we can do instead is rebind the discriminee to this branch's constructor, in the environment the body is evaluated in and in the one the type is re-evaluated in.  That refines the *value* as well as the type, which is what keeps the two in step: the body evaluates to what it was checked to be, and occurrences of the discriminee in it display as the constructor.  This needs a non-modal match on a bare variable at dimension zero, in environments that rebind_level can push a value back into; when any of that fails we let the error through, and the caller reads the branch back unrefined instead. *)
                                        let refined () =
                                          let envdim = Modality.filtered env_dim fw in
                                          (* The dimension we are stuck at splits as the environment's dimension plus the match's own.  Each variable of the branch's context is a cube of the *environment's* dimension, while the constructor and the indices are cubes of the total one; so over each face of the match's own dimension there sits one variable, holding the cube of instances at that face.  For the top face that variable is the discriminee, and for the others they are the instantiation arguments of its type -- which is exactly the cube of variables check_var_match rebinds.  Slicing this way covers both ways the dimension can arise, and their combination: a degenerated definition has no match dimension, a match on a variable of higher-dimensional type has no environment dimension, and a degenerated definition containing such a match has both. *)
                                          (* The variables sitting over each face of the match's own dimension, paired with the values that replace them.  The top face is the discriminee, which the caller passes separately, so we can skip it. *)
                                          let face_rebindings ~skip_top vars vals =
                                            let acc = ref [] in
                                            CubeOf.miter
                                              {
                                                it =
                                                  (fun fn [ v ] ->
                                                    if skip_top && Option.is_some (is_id_sface fn)
                                                    then ()
                                                    else
                                                      Option.iter
                                                        (fun l ->
                                                          acc :=
                                                            (l, CubeOf.slice envdim plus_dim vals fn)
                                                            :: !acc)
                                                        (level_of_free_var window v.tm));
                                              }
                                              [
                                                CubeOf.build match_dim
                                                  {
                                                    build =
                                                      (fun fn ->
                                                        let (Plus kp) = D.plus (dom_sface fn) in
                                                        CubeOf.find vars
                                                          (sface_plus_sface (id_sface envdim)
                                                             plus_dim kp fn));
                                                  };
                                              ];
                                            !acc in
                                          match level_of_free_var window disc with
                                          | Some disc_level -> (
                                              let ccube = constr_cube constr total_dim newvars in
                                              let disc_vars =
                                                TubeOf.plus_cube disc_tyargs
                                                  (CubeOf.singleton
                                                     { tm = disc; ty = Lazy.from_val discty }) in
                                              let index_rebindings =
                                                match data_indices with
                                                | Unfilled _ -> []
                                                | Filled var_indices ->
                                                    List.concat
                                                      (Vec.to_list
                                                         (Vec.mmap
                                                            (fun [ old; nw ] ->
                                                              face_rebindings ~skip_top:false old
                                                                (CubeOf.mmap
                                                                   { map = (fun _ [ x ] -> x.tm) }
                                                                   [ nw ]))
                                                            [
                                                              var_indices;
                                                              indices_of_out "match branch" out
                                                                total_dim (Vec.length var_indices);
                                                            ])) in
                                              match
                                                rebind_branch ctx env window
                                                  (List.append index_rebindings
                                                     (face_rebindings ~skip_top:true disc_vars ccube))
                                                  ( disc_level,
                                                    CubeOf.slice envdim plus_dim ccube
                                                      (id_sface match_dim) )
                                              with
                                              | Some (renv, rctxenv) -> (
                                                  (* Re-evaluating the self across the rebinding makes its spine reduce, which is what a higher field's instances need in order to survive being degenerated. *)
                                                  match
                                                    eval_term rctxenv
                                                      (readback_neu ctx head_head head_args)
                                                  with
                                                  | Neu { head = rhead; args = rargs; _ } ->
                                                      branch rhead rargs
                                                        (take_args renv plus_dim newvars window fw
                                                           annotate comp)
                                                        (eval_term rctxenv
                                                           (readback_val ctx match_ty))
                                                  | _ ->
                                                      fatal
                                                        (Anomaly
                                                           "refined self of a stuck match is not neutral")
                                                  )
                                              | None ->
                                                  fatal
                                                    (Anomaly "can't rebind stuck match discriminee")
                                              )
                                          | None ->
                                              fatal (Anomaly "can't rebind stuck match discriminee")
                                        in
                                        (* We try to refine first, and read the branch back unrefined only if that fails -- as typechecking tries a variable match before falling back to a non-dependent one.  When the discriminee is a variable, refining is the reading that matches what was checked; when it isn't, there is nothing to rebind and the type we were handed (or the one the motive gives) is already the type of every branch. *)
                                        Reporter.try_with ~fatal:(fun _ ->
                                            branch head_head head_args
                                              (take_args env plus_dim newvars window fw annotate
                                                 comp)
                                              branch_ty)
                                        @@ fun () -> refined ())
                                  branches in
                              Some
                                (rewrap
                                   (Term.Match
                                      {
                                        tm = disc_tm;
                                        window;
                                        plus_lock = new_plus_lock;
                                        dim = total_dim;
                                        (* The output is display-only and the unparser doesn't show a motive, so we don't read one back. *)
                                        motive = None;
                                        branches = new_branches;
                                      })))
                      | None -> no_display "a stuck match whose own neutral could not be recovered")
                  | _ -> no_display "a stuck match that is not a neutral"))
          | _ -> fatal (Anomaly "discriminee of a stuck match is not of a datatype")))
  | _ -> no_display "a stuck metavariable"

(* ********** Readback of comatches (for display only) ********** *)

(* Read back one higher field of a comatch, as the PlusPbijmap of instances that Structfield.Higher stores: one entry per partial bijection between the comatch's dimension and the field's intrinsic dimension.

   The entry at a pbij with 'r remaining dimensions must be a term over the ambient context *degenerated by 'r*, since that is where such a component is checked and where its type lives.  So, exactly as check_higher_field does, we degenerate the context by those dimensions, commute the degeneracy past the right-adjoint lock, and lock the degenerated context to it.  The body is then the comatch's stored term for the corresponding term-level pbij, evaluated in its closure environment transported into that degenerated context -- an eval-readback through the stored termctx, which is why Structfield.Higher records one.

   The whole field gives up (None) if the comatch carries no termctx (a hand-built fibrancy field) or if some instance is a genuinely stuck case tree. *)
and readback_higher_comatch_field : type mode a z m i f g gmode aa hm hn hmn ag.
    (mode, z, a) Ctx.t ->
    (mode, m, D.zero, aa, no_eta) Value.codata_args ->
    (* The neutral whose potential value is the comatch, serving as the self-variable, and its type. *)
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    m D.t ->
    i Field.t ->
    (mode, f, g, gmode) Modalcell.adjunction ->
    (mode, f, g, gmode, hm, hn, hmn, m, i, ag) Value.Structfield.higher_data ->
    (i, mode * (m * a * potential * no_eta)) Term.Structfield.t option =
 fun ctx codata_args neutral ty dim fld adj hd ->
  ignore (codata_args, hd);
  let exception Unprojectable_self in
  try
    let (Adjunction { left; right; unit; _ }) = adj in
    let (Locked
           (type ag2)
           ((ctx_plus_lock, _) : (a, mode, g, gmode, ag2) plus_lock * (gmode, z, ag2) Ctx.t)) =
      Ctx.lock ctx right in
    (* The self, keyed by the adjunction unit, and its type, exactly as for a lower field. *)
    let selfnf =
      {
        tm = Act.act_value neutral (id_deg D.zero) unit;
        ty = lazy (Act.act_ty neutral ty (id_deg D.zero) unit);
      } in
    let pbm =
      Term.PlusPbijmap.build dim (Field.dim fld)
        {
          build =
            (fun (type r) (pbij : (m, i, r) pbij) : (r, gmode * ag2) Term.PlusFam.t ->
              let (Pbij (fldins, fldshuf)) = pbij in
              let r = left_shuffle fldshuf in
              (* The instance's body lives in the context degenerated by its remaining dimensions, so we build it there, as check_higher_field does: degenerate the context, commute the degeneracy past the right-adjoint lock, and lock the degenerated context to it. *)
              let (Degctx (plusmap, dctx, denv)) = degctx ctx r in
              let (Shift (plusmap_bg, deg_plus_lock)) = shift_unplus_lock r plusmap ctx_plus_lock in
              let dlctx = Ctx.lock_to dctx right deg_plus_lock in
              (* Raise the self into that context, where the remaining dimensions are genuine dimensions and this instance is therefore *projectable*: ins_plus_of_pbij absorbs them into the evaluation dimension, turning the partial bijection into an insertion.  This is the move check_higher_field makes to carry its status into a component.  The body is then just a field projection read back like a lower field's -- the comatch's closure environment never has to be transported, and no shuffleable is needed, since at this dimension nothing remains. *)
              let dself = degenerate_normal ctx denv r selfnf in
              (* Degenerating the self reads it back and re-evaluates it, so it survives that round trip only if its spine really does evaluate to the comatch.  An ordinary self does; the one readback_stuck_match supplies in a match branch does not, when it could not refine the discriminee -- there the spine is still a stuck match, so projecting from it computes nothing and we would show an instance body that is not the one the comatch stores.  We detect that and abandon the whole field, rather than returning None, which would mean the weaker thing that this *instance* is absent. *)
              (match dself.tm with
              | Neu { value; _ } -> (
                  match force_eval value with
                  | Val (Struct _) -> ()
                  | _ -> raise_notrace Unprojectable_self)
              | _ -> raise_notrace Unprojectable_self);
              let (Plus rm) = D.plus dim in
              let newins = ins_plus_of_pbij fldins fldshuf rm in
              let ety = tyof_field left (Ok dself.tm) (Lazy.force dself.ty) fld newins in
              Some
                (Term.PlusFam.PlusFam
                   ( plusmap_bg,
                     Term.Realize
                       (readback_at Kinetic dlctx (field_term left dself.tm fld newins) ety) )));
        } in
    Some (Term.Structfield.Higher (adj, ctx_plus_lock, pbm))
  with Unprojectable_self ->
    no_display "a higher field of a comatch in a match branch whose discriminee was not refined"

(* To read back a comatch, we need the *neutral* whose value is the comatch, so as to use that neutral itself as the self-variable for computing each field's type with tyof_field (the neutral is already in the context, so no fresh self is needed; being Const-headed, it reads back without a context level).  A lower field is projected from the neutral directly, keying by the adjunction unit and reading the component back behind the right-adjoint lock (all trivial for an ordinary non-modal field).  A higher field's instances are read back by readback_higher_comatch_field above.

   The eta and no-eta cases go through the same code: the return-type annotation keeps the field-map's eta ('et) polymorphic, and the higher-field branch constrains 'et = no_eta only locally where it is actually reached.  So a record, which has no higher fields, reads back its (non-leaf) tuple value here too, which is what lets "about (Prod A B)⁽ᵉ⁾ .trr p" display the componentwise transport rather than the stuck spine.

   A field whose left adjoint filters this dimension nontrivially disappears here, exactly as it does for projection and for the codatatype display, so it is not displayed at all.  The result is None if a higher field could not be read back. *)
and readback_comatch : type mode a z.
    (mode, z, a) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, a, potential) term option =
 fun ctx neutral ty ->
  match (neutral, view_type ty "readback_comatch") with
  | ( Neu { value = nval; _ },
      Canonical
        (type hmode mn m n)
        ((_, Codata (type aa et) (codata_args : (mode, m, n, aa, et) codata_args), ins, _) :
          (hmode, kinetic) head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t) ) -> (
      match force_eval nval with
      | Val
          (Struct
             (type p k pk vet)
             ({ fields = comatch_fields; ins = value_ins; _ } :
               (mode, p, k, pk, potential, vet) Value.struct_args)) -> (
          let dim = cod_left_ins ins in
          let evaldim = dim_env codata_args.env in
          match D.compare (cod_left_ins value_ins) dim with
          | Neq -> fatal (Anomaly "comatch readback: struct dimension does not match its type")
          | Eq ->
              let fields =
                Bwd.fold_left
                  (fun acc
                       (Term.CodatafieldAbwd.Entry
                          (type i)
                          ((fld, Codatafield ((Adjunction { left; right; unit; _ } as adj), _, cf)) :
                            i Field.t * (i, mode * aa * D.zero * n * et) Term.Codatafield.t)) :
                       (mode * (m * a * potential * et)) Term.StructfieldAbwd.t option ->
                    let (Has_filter lfilter) = Modality.filter left dim in
                    match Modality.filter_is_trivial dim lfilter with
                    | None -> acc
                    | Some Eq -> (
                        match (acc, cf) with
                        | None, _ -> None
                        | Some acc, Lower _ ->
                            (* Project the field from the neutral-as-self, keying by the adjunction unit and reading back the component behind the right-adjoint lock. *)
                            let xu = Act.act_value neutral (id_deg D.zero) unit in
                            let tyu = Act.act_ty neutral ty (id_deg D.zero) unit in
                            let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                            Some
                              (Snoc
                                 ( acc,
                                   Term.StructfieldAbwd.Entry
                                     ( fld,
                                       Term.Structfield.Lower
                                         ( adj,
                                           plus_lock,
                                           Term.Realize
                                             (readback_at Kinetic lctx
                                                (field_term left xu fld (ins_zero dim))
                                                (tyof_field left (Ok xu) tyu fld (ins_zero evaldim))),
                                           `Labeled ) ) ))
                        | Some acc, Higher _ -> (
                            match Value.StructfieldAbwd.find_opt comatch_fields fld with
                            | Found (Value.Structfield.Higher (lazy hd)) -> (
                                (* The comatch stores its own copy of the field's adjunction, whose existential types are a priori unrelated to those of the declaration; match them up so the stored bodies can be read back at the declared field type.  A value checked against this declaration must carry the declared adjunction, so a mismatch is a bug. *)
                                match Modalcell.compare_adjunction hd.adj adj with
                                | Neq ->
                                    fatal
                                      (Anomaly
                                         "comatch readback: field adjunction does not match its declaration")
                                | Eq -> (
                                    match
                                      readback_higher_comatch_field ctx codata_args neutral ty dim
                                        fld adj hd
                                    with
                                    | None -> None
                                    | Some sf ->
                                        Some (Snoc (acc, Term.StructfieldAbwd.Entry (fld, sf)))))
                            | _ ->
                                fatal
                                  (Anomaly "comatch readback: higher field missing from comatch"))))
                  (Some Emp) codata_args.fields in
              Option.map
                (fun fields ->
                  Term.Struct { eta = codata_args.eta; dim; fields; energy = Potential })
                fields)
      | _ -> fatal (Anomaly "comatch readback: neutral value is not a struct"))
  | _ -> fatal (Anomaly "comatch readback: not a neutral at a codatatype")

(* The "about" command reads back the *potential* value of a neutral, passing the neutral itself as readback's status so that a canonical type displays as its declaration and a comatch as itself; readback_at handles the rest, including descending through parameter abstractions.  None means the neutral has no potential value at all to display -- an axiom, or a permanently stuck case tree -- so the caller shows its normal form instead. *)
let readback_about : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) Value.value -> (mode, b, potential) Term.term option =
 fun ctx value ->
  match value with
  | Neu { value = v; ty; _ } -> (
      match force_eval v with
      | Val v -> Some (readback_at (Potential value) ctx v (Lazy.force ty))
      (* A neutral whose case tree got stuck on a match displays as that match. *)
      | Unrealized (Some pn) -> readback_stuck (Potential value) ctx pn (Lazy.force ty)
      | _ -> None)
  | _ -> None
