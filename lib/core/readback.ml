open Bwd
open Util
open Modal
open Tlist
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

(* Degenerating a context by a dimension (for the non-projectable instances of higher codata fields, when displaying a codatatype or comatch for "about").  The degeneration itself is implemented in the downstream module Degctx, because it does an eval-readback cycle and hence depends on this file; but the "about" display code that consumes it lives here (below), so we make the degeneration a forward reference set by Degctx.  The result packages the degeneration plus-map, the degenerated context, and the canonical k-dimensional environment from it back to the original. *)
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

(* Readback of values to terms.  Closely follows equality-testing in equal.ml, so most comments are omitted.  However, unlike equality-testing and the "readback" in theoretical NbE, this readback does *not* eta-expand functions and tuples.  It is used for (1) displaying terms to the user, who will usually prefer not to see things eta-expanded, and (2) turning values into terms so that we can re-evaluate them in a new environment, for which purpose eta-expansion is irrelevant.  There are two exceptions:

   1. When reading back at a record type that the user has marked as transparent, we eta-expand tuples.  This is chosen based on the readback type.
   2. When reading back a higher-dimensional pi-type, we eta-expand its instantiation arguments so that we can display it prettily.  This is controlled by the flag ~eta. *)

let rec readback_nf : type mode a z.
    ?eta:bool -> (mode, z, a) Ctx.t -> mode normal -> (mode, a, kinetic) term =
 fun ?(eta = false) n x -> readback_at ~eta n x.tm x.ty

(* Read back an evaluation: a Val recurses, a Realize wraps the (kinetic) realization in Realize, and an Unrealized (a genuinely stuck case tree) can't be read back as a value.  This is how we read back the result of *applying* a potential value (a case-tree lambda); for a kinetic value, apply always returns Val, so only that arm is live. *)
and readback_eval : type mode a z s.
    ?eta:bool ->
    (mode, z, a) Ctx.t ->
    (mode, s) evaluation ->
    (mode, kinetic) value ->
    (mode, a, s) term =
 fun ?(eta = false) ctx ev ty ->
  match ev with
  | Val v -> readback_at ~eta ctx v ty
  | Realize v -> Realize (readback_at ~eta ctx v ty)
  | Unrealized -> fatal (Anomaly "unrealized value in readback")

(* Readback is energy-polymorphic: it reads back a value of any energy 's into an ('a, 's) term.  In practice it is only ever called on a *potential* value by "about" (which reads back the forced value of a neutral); that's the only way a comatch (a no-eta struct) reaches the Codata branch and gets eta-expanded.  All other callers read back kinetic values (neutrals, etc.) and get their application spines as before. *)
and readback_at : type mode a z s.
    ?eta:bool -> (mode, z, a) Ctx.t -> (mode, s) value -> (mode, kinetic) value -> (mode, a, s) term
    =
 fun ?(eta = false) ctx tm ty ->
  let view = if Displaying.read () then view_term tm else tm in
  let vty = view_type ty "readback_at" in
  match (vty, view) with
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
          let body = readback_eval ~eta newctx (apply tm filter args) output in
          Term.Lam (x, n, filter, body))
  (* If eta-expansion is enabled, we do an eta-expanding readback of any term. *)
  | Canonical (_, Pi { x = name; filter; doms; cods }, ins, tyargs), tm when eta ->
      let modality = Modality.filter_modality filter in
      let Eq = eq_of_ins_zero ins in
      let name = View.fill_hints doms name in
      let newargs, newnfs = dom_vars ctx modality doms in
      let (Any_ctx newctx) = Ctx.variables_vis ctx (Modality.filter_idempotent filter) name newnfs in
      let output = tyof_app cods tyargs filter newargs in
      (* We carry through the eta-expansion flag so that iterated pi-types will eta-expand fully. *)
      Term.Lam
        (name, BindCube.dim cods, filter, readback_eval ~eta newctx (apply tm filter newargs) output)
  | ( Canonical
        (type hmode mn m n)
        (( _,
           Codata
             (type c a et)
             ({ eta; opacity; fields; env = _; termctx = _; hints = _ } :
               (mode, m, n, c, a, et) codata_args),
           ins,
           _ ) :
          hmode head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      _ ) -> (
      match eta with
      (* A no-eta codatatype: an ordinary readback of a (kinetic) neutral here yields its application spine.  Displaying a comatch as a comatch is done by "about" via readback_comatch, which forces the neutral's potential value; it is not reached through readback_at. *)
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
                                (adj', plus_lock, readback_at lctx (force_eval_term fldtm) ety, lbl)
                            ))
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
                            ((_, Lower (Adjunction { left; _ }, _, _)) :
                              i Field.t * (i, mode * a * n * has_eta) Codatafield.t)) ->
                      let (Has_filter left_filter) = Modality.filter left m in
                      match Modality.filter_is_trivial m left_filter with
                      | Some Eq -> true
                      | None -> false)
                    fields in
                let fields =
                  Mbwd.map
                    (fun (CodatafieldAbwd.Entry
                            (type i)
                            ((fld, Lower ((Adjunction { left; right; unit; _ } as adj), _, _)) :
                              i Field.t * (i, mode * a * n * has_eta) Codatafield.t)) ->
                      (* Eta-expansion of a modal field: key the term by the adjunction unit, project, and read back the component in the context locked by the right adjoint (as in the eta-rule for equality). *)
                      let xu = act_value tm (id_deg D.zero) unit in
                      let tyu = act_ty tm ty (id_deg D.zero) unit in
                      let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                      Term.StructfieldAbwd.Entry
                        ( fld,
                          Term.Structfield.Lower
                            ( adj,
                              plus_lock,
                              readback_at lctx (field_term left xu fld fldins)
                                (tyof_field left (Ok xu) tyu fld ~shuf:Trivial fldins),
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
                | Some res -> Act (res, deg_of_perm p, (`Other, `Other))
                | None -> readback_val_sorted ctx rtm vty) in
          match view with
          | Struct { energy = Kinetic; _ } -> do_record view
          | Neu _ -> do_record view
          | _ -> readback_val_sorted ctx tm vty))
  | Canonical (_, Data { constrs; _ }, ins, tyargs), Constr (xconstr, xn, xargs) -> (
      let Eq = eq_of_ins_zero ins in
      (* Pick out the constructor of the datatype that matches the one we're reading back *)
      let (Dataconstr { env; args = argtys; output = _ }) =
        Abwd.find_opt xconstr constrs <|> Anomaly "constr not found in readback" in
      match D.compare xn (TubeOf.inst tyargs) with
      | Neq -> fatal (Dimension_mismatch ("reading back constrs", xn, TubeOf.inst tyargs))
      | Eq ->
          (* We need the same number of arguments as there are types in the telescope. *)
          let lgth = Telescope.length argtys in
          let xargs =
            Vec.of_list_length lgth xargs
            <|> Anomaly "wrong number of constructor arguments in readback_at" in
          (* If a higher-dimensional constructor belongs to a higher version of a datatype, the instantiation arguments of the latter must be lower-dimensional versions of the same constructor.  We extract their arguments to form the boundaries of the types of the arguments of our current constructor. Specifically, tyargs is a tube of normals, each of which is expected to be a lower-dimensional instance of the same constructor, which therefore has a list of modal cubes as arguments.  We want to extract the top element of each of those cubes to form a *list of tubes* of modal values, whereas what we naturally have, after peeling off the constructors, is a *tube of lists*.  We do the conversion with our multiple-output traversal with a variable number of outputs, specifically the length of the telescope. *)
          let (Conses (cs, bs)) = Tlist.conses lgth in
          let tyarg_args =
            TubeOf.Heter.vec_of_hgt cs
            @@ TubeOf.pmap
                 {
                   map =
                     (fun _ [ tm ] ->
                       match view_term tm.tm with
                       | Constr (tmname, _, tmargs) ->
                           if tmname = xconstr then
                             let ys =
                               Vec.of_list_length_map
                                 (fun (Value.Modal (xfilt, x)) : (_, _) modal_value ->
                                   Modal (Modality.filter_modality xfilt, CubeOf.find_top x))
                                 lgth tmargs
                               <|> Anomaly "inst arg wrong num args in readback at datatype" in
                             CubeOf.Heter.hft_of_vec cs ys
                           else fatal (Anomaly "inst arg wrong constr in readback at datatype")
                       | _ -> fatal (Anomaly "inst arg not constr in readback at datatype"));
                 }
                 [ tyargs ] bs in
          (* Now xargs, argtys, and tyarg_args are all guaranteed to have the same length, so readback_at_tel doesn't have to worry. *)
          Constr (xconstr, dim_env env, readback_at_tel ctx env xargs argtys tyarg_args))
  | _ -> readback_val_sorted ctx tm vty

and readback_val_sorted : type mode a z s.
    (mode, z, a) Ctx.t -> (mode, s) value -> mode View.view_type -> (mode, a, s) term =
 fun ctx tm vty ->
  let sort = sort_of_ty ctx vty in
  readback_val ~sort ctx tm

(* The synthesizing readback only ever applies to neutrals (a kinetic value); any other value reaching it (which can only be a potential value, since other callers pass kinetic neutrals) is an anomaly. *)
and readback_val : type mode a z s.
    ?sort:[ `Type | `Function | `Other ] ->
    (mode, z, a) Ctx.t ->
    (mode, s) value ->
    (mode, a, s) term =
 fun ?(sort = `Other) ctx x ->
  match x with
  | Neu { head; args; value; ty } -> (
      match (force_eval value, Displaying.read ()) with
      | Realize v, true -> readback_at ctx v (Lazy.force ty)
      | Val (Canonical _), _ -> readback_neu ~sort:(sort, `Canonical) ctx head args
      | _ -> readback_neu ~sort:(sort, `Other) ctx head args)
  | Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing readback")
  | Struct _ -> fatal (Anomaly "unexpected struct in synthesizing readback")
  | Constr _ -> fatal (Anomaly "unexpected constr in synthesizing readback")
  | Canonical _ -> fatal (Anomaly "unexpected canonical in synthesizing readback")

and readback_neu : type hmode mode a z any.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (mode, z, a) Ctx.t ->
    hmode head ->
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
        ( App
            ( readback_neu ~sort ctx head apps,
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
          Term.Act (Field (Modal (fm, plus_lock, inner), fld, id_ins t fldplus), p, sort)
      | None ->
          (* Nontrivial filter: the field's modality is nonparametric and a degeneracy has acted, so the inner spine lives at a strictly smaller filtered dimension ft than the result dimension t.  We read back the projection at ft and lift it to t by the filter's degeneracy, which reconstructs (and prints as) the acting degeneracy — this is exactly the "disappeared" projection viewed as a degeneracy of a lower-dimensional one, and it re-evaluates correctly since eval filters the environment dimension. *)
          let ft = Modality.filtered t filter in
          let (Plus new_fldplus) = D.plus (D.plus_right fldplus) in
          let fieldterm : (_, _, kinetic) Term.term =
            Term.Field (Modal (fm, plus_lock, inner), fld, id_ins ft new_fldplus) in
          let liftdeg = Modality.deg_of_filter t filter in
          Term.Act (Term.Act (fieldterm, liftdeg, sort), p, sort))
  | Inst (Emp, _, args), Pi _ when TubeOf.is_full args ->
      (* When reading back a fully instantiated higher-dimensional pi-type, we eta-expand the instantiation arguments so that it can be printed with a nice notation. *)
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ~eta:true ctx x) } [ args ] in
      Inst (readback_head ~sort ctx head, args)
  | Inst (apps, _, args), _ ->
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ args ] in
      Inst (readback_neu ~sort ctx head apps, args)

and readback_head : type mode c z.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (mode, z, c) Ctx.t ->
    mode head ->
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
            | None -> Act (Term.Var (Index (insert, fa, filter, iplus)), deg, sort) in
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
      | None -> Act (Const name, deg, sort))
  | Meta { meta; env; ins } -> (
      let tm = MetaEnv (meta, readback_env ctx env (Global.find_meta meta).termctx) in
      match is_id_ins ins with
      | Some _ -> tm
      | None ->
          let (To perm) = deg_of_ins ins in
          Act (tm, perm, sort))
  | UU (mode, n) -> UU (mode, n)
  | Pi (type dom modality k n) ({ x; filter; doms; cods } : (dom, modality, mode, k, n) pi_args) ->
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
      Pi
        {
          x;
          filter;
          doms =
            Modal
              ( modality,
                plus,
                CubeOf.mmap { map = (fun _ [ dom ] -> readback_val ~sort:`Type lctx dom) } [ doms ]
              );
          cods = CodCube.build n { build };
        }

(* Read back a vector of values, with their types specified in a term telescope.  The environment is used for evaluating each type at the previous values, for use in reading back the later values.  Each type also has to be instantiated at a boundary, supplied as a vector of tubes. *)
and readback_at_tel : type mode n c a b ab z.
    (mode, z, c) Ctx.t ->
    (mode, n, a) env ->
    ((n, mode, kinetic) modal_value_cube, b) Vec.t ->
    (mode, a, b, ab) Telescope.t ->
    ((D.zero, n, n, (mode, kinetic) modal_value) TubeOf.t, b) Vec.t ->
    (n, mode, c, kinetic) any_modal_term_cube list =
 fun ctx env xs tys tyargs ->
  match (xs, tys, tyargs) with
  | [], Emp, [] -> []
  | ( Modal
        (type dom modality k)
        ((filter, x) :
          (dom, modality, mode, k, n) Modality.filter_dim * (k, (dom, kinetic) value) CubeOf.t)
      :: xs,
      Ext (_, Modal (tymodality, aplus, ty), tys),
      tyargs :: tyargs_rest ) -> (
      let xmodality = Modality.filter_modality filter in
      match Modality.compare xmodality tymodality with
      | Neq -> fatal (Modality_mismatch (`Internal, "readback_at_tel", xmodality, tymodality))
      | Eq ->
          let (Locked (cplus, lctx)) = Ctx.lock ctx tymodality in
          let lenv = key_id_env env aplus in
          let x = CubeOf.find_top x in
          let ety = eval_term lenv ty in
          (* The argument is k-dimensional, where k is the modal filtering of the dimension n of the entire constructor.  We build k-cubes of read-back terms and values in parallel. *)
          let n = dim_env env in
          let k = Modality.filtered n filter in
          let tyargtbl = Hashtbl.create 10 in
          let [ tyarg; tms ] =
            TubeOf.pbuild D.zero (D.zero_plus k)
              {
                build =
                  (fun fa ->
                    (* The value associated to some face of k in the cube of arguments is derived from the corresponding argument of the n-dimensional constructor associated to the corresponding face of n lifted along the filter.  This makes sense because when a constructor is evaluated, the modally filtered arguments are degenerated to obtain values for the boundary constructors, and the face and degeneracy cancel out. *)
                    let (Pface_filter (_, fb)) = Modality.pface_filter n fa filter in
                    let (Modal (argmod, argtm)) = TubeOf.find tyargs fb in
                    match Modality.compare argmod xmodality with
                    | Neq ->
                        fatal (Modality_mismatch (`Internal, "readback_at_tel", argmod, tymodality))
                    | Eq ->
                        let fa = sface_of_tface fa in
                        let fb = sface_of_tface fb in
                        let argty : (dom, kinetic) value =
                          inst
                            (eval_term
                               (act_env lenv
                                  (opt_op_of_opt_sface
                                     (comp_opt_sface
                                        (Modality.sface_of_filter n filter)
                                        (opt_of_sface fa))))
                               ty)
                            (TubeOf.build D.zero
                               (D.zero_plus (dom_sface fb))
                               {
                                 build =
                                   (fun fc ->
                                     Hashtbl.find tyargtbl
                                       (SFace_of (comp_sface fb (sface_of_tface fc))));
                               }) in
                        let argnorm : dom normal = { tm = argtm; ty = argty } in
                        let argtm = readback_at lctx argtm argty in
                        Hashtbl.add tyargtbl (SFace_of fb) argnorm;
                        [ argnorm; argtm ]);
              }
              (Cons (Cons Nil)) in
          let ity = inst ety tyarg in
          Modal (filter, cplus, TubeOf.plus_cube tms (CubeOf.singleton (readback_at lctx x ity)))
          :: readback_at_tel ctx
               (Ext
                  {
                    env;
                    plus = D.plus_zero (TubeOf.inst tyarg);
                    values = `Ok (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x));
                    filter;
                    filtered = Modality.filter_zero xmodality;
                  })
               xs tys tyargs_rest)

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
                    Hashtbl.add xtytbl (SFace_of fb) { tm; ty };
                    (* Finally, we read back the term in that instantiated type. *)
                    readback_at lctx tm ty);
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

let readback_bindings : type mode a b n.
    (mode, a, b) Ctx.t -> (n, mode Binding.t) CubeOf.t -> (n, (mode, b) binding) CubeOf.t =
 fun ctx vbs ->
  CubeOf.mmap
    {
      map =
        (fun _ [ b ] ->
          match Binding.level b with
          | Some _ ->
              ({ tm = None; ty = readback_val ~sort:`Type ctx (Binding.value b).ty }
                : (mode, b) binding)
          | None ->
              {
                tm = Some (readback_nf ctx (Binding.value b));
                ty = readback_val ~sort:`Type ctx (Binding.value b).ty;
              });
    }
    [ vbs ]

type (_, _, _, _, _, _) readback_entry =
  | Readback_entry :
      ('dom, 'modality, 'mode, 'b, 'bm, 'f, 'n) entry
      -> ('dom, 'modality, 'mode, 'b, 'f, 'n) readback_entry

let readback_entry : type dom modality mode a b f n.
    (mode, a, (b, (modality, n) dim_entry) snoc) Ctx.t ->
    (dom, modality, mode, f, n) Ctx.entry ->
    (dom, modality, mode, b, f, n) readback_entry =
 fun ctx e ->
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
                (tyof_field (Modality.id (Ctx.mode lctx)) (Ok top.tm) top.ty f ~shuf:Trivial fins)
            in
            (f, x, fldty))
          fields in
      let bindings = readback_bindings lctx bindings in
      Readback_entry
        (Vis { dim; plusdim; plus_lock; vars; bindings; hasfields; fields; fplus; filter })
  | Invis { filter; bindings; _ } ->
      let modality = Modality.filter_modality filter in
      (* Invisible variables are anonymous, but we can still record display hints from their types, since after readback the types are terms and the hints can no longer be computed on demand.  Since this only affects display, if anything goes wrong computing the type (e.g. the binding is an error placeholder) we just skip the hints. *)
      let hints =
        Reporter.try_with ~fatal:(fun _ -> no_hints) @@ fun () ->
        View.hints_of_ty (Binding.value (CubeOf.find_top bindings)).ty in
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx modality in
      Readback_entry
        (Invis { plus_lock; filter; bindings = readback_bindings lctx bindings; hints })

let rec readback_ordered_ctx : type mode a b.
    (mode, a, b) Ctx.Ordered.t -> (mode, a, b) ordered_termctx = function
  | Emp mode -> Emp mode
  | Snoc (rest, e, af) as ctx ->
      let (Readback_entry re) = readback_entry (Ctx.of_ordered ctx) e in
      Ext (readback_ordered_ctx rest, re, af)
  | Lock (ctx, lock) -> Lock (readback_ordered_ctx ctx, lock)
  | Weaken (ctx, code) -> Weaken (readback_ordered_ctx ctx, code)

let readback_ctx : type mode a b. (mode, a, b) Ctx.t -> (mode, a, b) termctx = function
  | Permute { perm; ctx; _ } -> Permute (perm, readback_ordered_ctx ctx)

(* Readback of data types, for display. *)

(* The result of reading back a constructor's argument telescope from a value: the telescope as a term, plus the context and environment extended by fresh variables for its arguments (needed to read back the index values that follow it), and the (zero-dimensional) values of those fresh argument variables in order (needed to build the constructor-as-a-function for degenerate datatypes; we read them back via readback_at_tel). *)
type (_, _, _, _) readback_tel =
  | Readback_tel :
      ('mode, 'e, 'c, 'ec) Term.tel
      * ('mode, 'lev, 'ec) Ctx.t
      * ('mode, D.zero, 'ac) Value.env
      * ((D.zero, 'mode, kinetic) modal_value_cube, 'c) Vec.t
      -> ('mode, 'e, 'c, 'ac) readback_tel

(* Read back a (zero-dimensional) telescope of value-level types into a term-level telescope in the readback context, introducing a fresh variable for each entry.  Each entry may carry a modality (constructor arguments, unlike indices, can be modal); we evaluate its type under the corresponding lock and reconstruct the modal telescope entry over the readback context, following check_tel/ext_tel. *)
let rec readback_tel : type mode lev e a c ac.
    (mode, lev, e) Ctx.t ->
    (mode, D.zero, a) Value.env ->
    (mode, a, c, ac) Term.tel ->
    (mode, e, c, ac) readback_tel =
 fun ctx env tel ->
  match tel with
  | Emp -> Readback_tel (Emp, ctx, env, [])
  | Ext (name, Modal (modality, plus, rty), rest) ->
      let m = dim_env env in
      let lenv = key_env env (Modalcell.id modality) plus in
      let ety = Norm.eval_term lenv rty in
      (* The environment is zero-dimensional, so the annotation's dimension filter is its zero filter. *)
      let filter = Modality.filter_zero modality in
      let newvars, newnfs =
        Domvars.dom_vars ctx modality
          (CubeOf.build m
             { build = (fun fa -> Norm.eval_term (act_env lenv (opt_op_of_sface fa)) rty) }) in
      let (Locked (rplus, lctx)) = Ctx.lock ctx modality in
      let trty = readback_val ~sort:`Type lctx ety in
      let ctx = Ctx.cube_vis ctx (Modality.filter_idempotent filter) name newnfs in
      let env =
        Value.Ext
          {
            env;
            plus = D.plus_zero m;
            filter;
            filtered = Modality.filter_zero modality;
            values = `Ok newvars;
          } in
      let (Readback_tel (resttel, fctx, fenv, restargvals)) = readback_tel ctx env rest in
      Readback_tel
        ( Ext (name, Modal (modality, rplus, trty), resttel),
          fctx,
          fenv,
          Modal (filter, newvars) :: restargvals )

(* Read back a datatype definition. *)
let readback_data : type mode a b m j ij.
    (mode, a, b) Ctx.t ->
    ij Fwn.t ->
    (mode, kinetic) Value.value ->
    (mode, m, j, ij) Value.data_args ->
    (mode, b, potential) term =
 fun ctx indices tm { dim; constrs; discrete; recursive; tyfam; hints; indices = _ } ->
  let constrs =
    match (D.compare_zero dim, tm) with
    (* In the zero-dimensional case, we show each constructor with a telescope of arguments plus its output type.  The result ought to be re-evaluable, although we never need this. *)
    | Zero, _ ->
        Abwd.map
          (fun (Dataconstr { env; args; output }) ->
            (* To read back a value-level datatype constructor (at dimension zero) into the readback context, we read back its argument telescope, and its output type.  The output type is the stored output term (the datatype applied to the parameters and indices) evaluated at the fresh argument variables. *)
            let (Readback_tel (args, fctx, fenv, _)) = readback_tel ctx env args in
            let output = readback_val ~sort:`Type fctx (Norm.eval_term fenv output) in
            Term.Dataconstr { args; output })
          constrs
    | Pos _, Value.Neu { ty; _ } -> (
        (* In the positive-dimensional case, we want to show each constructor with its (higher-dimensional) function-type.  The caller has already forced tm to a Canonical datatype, so its type is a (degenerate) universe.  This is NOT re-evaluable. *)
        match View.view_type (Lazy.force ty) "degenerate_data_display" with
        | Canonical (_, UU (_, m), ins0, boundary) -> (
            let Eq = eq_of_ins_zero ins0 in
            (* The underlying zero-dimensional datatype is a vertex of the degenerate one, recovered from the boundary faces of its (degenerate-universe) type. *)
            let dom = TubeOf.plus_cube (val_of_norm_tube boundary) (CubeOf.singleton tm) in
            match vertex m with
            | Some v -> (
                (* When there is a vertex, we obtain the underlying zero-dimensional datatype d0 as a vertex of the degenerate one (a boundary face of its degenerate-universe type) and read back each constructor's function-type, instantiating the codomain at the lower-dimensional constructors. *)
                let d0 = CubeOf.find dom v in
                match View.view_type d0 "degenerate_data_display d0" with
                | Canonical (_, Data d0_args, _, _) -> (
                    match D.compare_zero d0_args.dim with
                    | Pos _ -> fatal (Anomaly "vertex of degenerate datatype is not 0-dimensional")
                    | Zero ->
                        (* A constructor's type is morally a function type "(args) → out", and the type of the degenerate constructor is the degeneration of that function.  To produce this, we form the constructor-as-a-function "λ args. c args" together with its function-type "(args) → out", and then act on it by the pure degeneracy deg_zero m using act_ty.  This instantiates its codomain at the faces of the function, which here are the lower-dimensional constructors, exactly producing e.g. "List⁽ᵉ⁾ (Id A) (cons. x₀ xs₀) (cons. x₁ xs₁)".  Reading back the result gives a higher-dimensional pi-type term, which unparses as "{x₀ x₁ : A} (x₂ : Id A x₀ x₁) … →⁽ᵉ⁾ …".  The constructor's output type "out" is the stored output term (e.g. "Vec A (suc. n)" for an indexed datatype, or the datatype itself for a non-indexed one) evaluated at the fresh argument variables. *)
                        Abwd.mapi
                          (fun c (Dataconstr { env; args; output }) ->
                            let (Readback_tel (tel, fctx, fenv, argvals)) =
                              readback_tel ctx env args in
                            let output_term =
                              readback_val ~sort:`Type fctx (Norm.eval_term fenv output) in
                            (* Build the constructor-as-a-function "λ args. c args".  The body "c args" is the constructor applied to its (just-bound) argument variables; we read those variables' values back into the extended context fctx with readback_at_tel (a zero-dimensional constructor, so the instantiation tube is empty), reusing the modal machinery that reads back any constructor's argument spine. *)
                            let cargs =
                              readback_at_tel fctx env argvals args
                                (Vec.mmap (fun [ _ ] -> TubeOf.empty D.zero) [ argvals ]) in
                            let cbody = Term.Constr (c, D.zero, cargs) in
                            let cfun = Telescope.lams tel cbody in
                            let cty = Telescope.pis tel output_term in
                            let cfun = Norm.eval_term (Ctx.env ctx) cfun in
                            let cty = Norm.eval_term (Ctx.env ctx) cty in
                            let ft =
                              Act.act_ty cfun cty (deg_zero m) (Modalcell.id2 (Ctx.mode ctx)) in
                            Pi_dataconstr (readback_val ~sort:`Type ctx ft))
                          d0_args.constrs)
                | _ -> fatal (Anomaly "vertex of degenerate datatype is not a datatype"))
            | None ->
                (* At a dimension with no endpoints, an m-cube has no proper faces, so we don't need the zero-dimensional base (which is unreachable anyway, as it would be a vertex of a faceless cube): we evaluate the constructor's function-type "(args) → output" directly in the degenerate (m-dimensional) environment that the constructor already carries.  There is still a (trivial, empty) instantiation, displayed as ".", so we instantiate the resulting m-dimensional function-type at the empty boundary tube before reading back.  Since the cube has no proper faces, the tube's builder is never called. *)
                Abwd.mapi
                  (fun _ (Dataconstr { env; args; output }) ->
                    let m = dim_env env in
                    let ft = Norm.eval_term env (Telescope.pis args output) in
                    let boundary =
                      TubeOf.build D.zero (D.zero_plus m)
                        { build = (fun _ -> fatal (Anomaly "boundary of vertex-free tube")) } in
                    Pi_dataconstr (readback_val ~sort:`Type ctx (Norm.inst ft boundary)))
                  constrs)
        | _ -> fatal (Anomaly "type of degenerate datatype is not a universe"))
    | _ -> fatal (Anomaly "degenerate datatype value is not neutral") in
  let tyfam = readback_nf ctx (nf_of_neu (force_eval_term tyfam) "readback_data") in
  Canonical (Data { indices; constrs; discrete; recursive; tyfam; hints })

(* ------------------------------------------------------------------------- *)
(* Reading back canonical types and (co)matches for the "about" command.      *)
(* ------------------------------------------------------------------------- *)

(* Build the "nontrivial shuffleable" passed to tyof_higher_codatafield when computing the type of a non-projectable instance of a higher codatatype field.  The remaining dimensions 'r have been split off, the context degenerated by them (degenv, of the degenerated ambient context), and the field's shuffle is fldshuf.  Its callbacks eval-readback values and environments to move them into the degenerated context. *)
let higher_codatafield_shuffleable : type mode a b c d r h i.
    (mode, a, b) Ctx.t ->
    (mode, c) Tctx.t ->
    (mode, d, (c, (mode id, D.zero) dim_entry) snoc) termctx ->
    (mode, r, b) env ->
    r D.t ->
    (r, h, i) shuffle ->
    (mode, r, h, i, c) shuffleable =
 fun ctx dbwd termctx degenv r fldshuf ->
  Nontrivial
    {
      dbwd;
      shuffle = fldshuf;
      deg_env = (fun _sh r_sh e -> eval_env degenv r_sh (readback_env ctx e termctx));
      deg_nf =
        (fun nf ->
          let ctm = readback_nf ctx nf in
          let tm = eval_term degenv ctm in
          let cty = readback_val ctx nf.ty in
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
                    let nf = { tm = fatm; ty = faty } in
                    Hashtbl.add argstbl (SFace_of (sface_of_tface fa)) nf;
                    nf);
              } in
          { tm; ty = inst ity tyargs });
    }

(* Raised by the comatch readback when it can't (yet) handle a field, so that "about" falls back to displaying the stored case tree (which unparse_comatch can render). *)
exception Comatch_fallback

(* Building the display node for a value-level codatatype or record type, for the "about" command.  This is the codata analogue of the datatype display builders in Readback (data_display_value / degenerate_data_display).  It lives here rather than in Readback because non-projectable higher-field instances are displayed in a context degenerated by their remaining dimensions (Degctx.degctx), and Degctx itself depends on Readback, so Readback cannot depend on Degctx.

   We introduce a single self-variable cube of the codatatype's dimension (via dom_vars, which gives its top face the fully-instantiated codatatype as its type), and read back the type of each field instance referring to it.  A lower field has exactly one instance; a higher field of intrinsic dimension i has one instance for each partial bijection between the codatatype's evaluation dimension and i.  Projectable instances (zero remaining dimensions) are read back in the self-variable context (Cfd); non-projectable ones (the declaration form ".e" and intermediate forms) are read back in a context degenerated by the remaining dimensions, recording the degeneration plus-map so the renderer can reconstruct the degenerated variable names (Cfd_deg).  The self-variable is added anonymously: readback ignores names (it produces de Bruijn terms), and the renderer chooses the displayed self-name itself. *)
let codata_display_value : type mode a b cm cn cc ca cet s.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) Value.value ->
    (mode, cm, cn, cc, ca, cet) Value.codata_args ->
    (mode, b, s) term =
 fun ctx tm codata_args ->
  let eta = codata_args.eta in
  let evaldim = dim_env codata_args.env in
  let self_modality = Modality.id (Ctx.mode ctx) in
  match tm with
  | Neu { ty; _ } -> (
      match view_type (Lazy.force ty) "codata_display_value" with
      | Canonical (_, UU (_, mk), ins0, boundary) ->
          (* The universe has intrinsic dimension zero, so its substitution dimension equals its total dimension mk. *)
          let Eq = eq_of_ins_zero ins0 in
          let dom = TubeOf.plus_cube (val_of_norm_tube boundary) (CubeOf.singleton tm) in
          let selfvars, selfnfs = dom_vars ctx self_modality dom in
          let self_top = CubeOf.find_top selfvars in
          let self_top_ty = (Ctx.Binding.value (CubeOf.find_top selfnfs)).ty in
          let ctx =
            Ctx.cube_vis ctx (Modality.filter_id (Ctx.mode ctx) (CubeOf.dim dom)) None selfnfs in
          let fields =
            Bwd.fold_left
              (fun acc
                   (Term.CodatafieldAbwd.Entry
                      (type i)
                      ((fld, cf) : i Field.t * (i, mode * ca * cn * cet) Term.Codatafield.t)) ->
                match cf with
                | Term.Codatafield.Lower (adj, _, _) -> (
                    (* "about" only displays non-modal codata fields, whose type lives at the codatatype's own mode; a genuinely modal field's type lives at the right adjoint's source mode and is not yet displayable. *)
                    match Modalcell.compare_adjunction_id adj with
                    | Neq -> fatal (Unimplemented "displaying modal codata fields")
                    | Eq ->
                        let ety : (mode, kinetic) value =
                          tyof_field (Modalcell.adj_left adj) (Ok self_top) self_top_ty fld
                            ~shuf:Trivial (ins_zero evaldim) in
                        Bwd.Snoc (acc, Term.Cfd (fld, [], readback_val ~sort:`Type ctx ety)))
                | Term.Codatafield.Higher (adj, _, _, _) -> (
                    match Modalcell.compare_adjunction_id adj with
                    | Neq -> fatal (Unimplemented "displaying modal codata fields")
                    | Eq ->
                        Seq.fold_left
                          (fun acc (Pbij_between (pbij : (cm, i, _) pbij)) ->
                            let (Pbij (fldins, fldshuf)) = pbij in
                            match D.compare_zero (left_shuffle fldshuf) with
                            | Zero ->
                                (* Projectable instance: read back in the self-variable context. *)
                                let Eq = eq_of_zero_shuffle fldshuf in
                                let ety : (mode, kinetic) value =
                                  tyof_field (Modalcell.adj_left adj) (Ok self_top) self_top_ty fld
                                    ~shuf:Trivial fldins in
                                Bwd.Snoc
                                  ( acc,
                                    Term.Cfd
                                      (fld, strings_of_pbij pbij, readback_val ~sort:`Type ctx ety)
                                  )
                            | Pos _ ->
                                (* Non-projectable instance: degenerate the context by the remaining dimensions and compute the field type there, recording the degeneration plus-map. *)
                                let r = left_shuffle fldshuf in
                                let (Degctx (plusmap, dctx, denv)) = degctx ctx r in
                                let termctx =
                                  Lazy.force codata_args.termctx
                                  <|> Anomaly "missing termctx for higher codata field" in
                                let shuf =
                                  higher_codatafield_shuffleable ctx (length_env codata_args.env)
                                    termctx denv r fldshuf in
                                let ety : (mode, kinetic) value =
                                  tyof_field (Modalcell.adj_left adj) (Ok self_top) self_top_ty fld
                                    ~shuf fldins in
                                Bwd.Snoc
                                  ( acc,
                                    Term.Cfd_deg
                                      ( fld,
                                        strings_of_pbij pbij,
                                        r,
                                        plusmap,
                                        readback_val ~sort:`Type dctx ety ) ))
                          acc
                          (all_pbij_between evaldim (Field.dim fld))))
              Bwd.Emp codata_args.fields in
          Term.Codata_display { eta; dim = mk; fields }
      | _ -> fatal (Anomaly "type of codatatype/record is not a universe"))
  | _ -> fatal (Anomaly "codatatype/record value is not neutral")

(* The forward-referenced implementation of comatch readback, type-directed by the codatatype, paralleling codata_display_value which reads back the field types.  It takes the *neutral* whose value is the comatch, and uses that neutral itself as the self-variable for computing each field's type with tyof_field (the neutral is already in the context, so no fresh self is needed; being Const-headed, it reads back without a context level).  A lower field is projected from the neutral directly.  A higher field's instances are read back from the comatch's stored terms, one per partial bijection: for each, we degenerate the readback context by the remaining dimensions, compute the field type there, evaluate the stored body term in the degenerated closure environment, and read it back.  For a top-level comatch the closure environment is empty, hence degeneration-invariant, so we evaluate directly in it; a non-empty closure environment (a partially-applied higher comatch) falls back to the stored case tree. *)
let readback_comatch_impl : type mode a z.
    (mode, z, a) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, a, potential) term =
 fun ctx neutral ty ->
  match (neutral, view_type ty "readback_comatch") with
  | ( Neu { value = nval; _ },
      Canonical
        (type hmode mn m n)
        ((_, Codata (type c aa et) (codata_args : (mode, m, n, c, aa, et) codata_args), ins, tyargs) :
          hmode head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t) ) -> (
      match force_eval nval with
      | Val (Struct { fields = comatch_fields; _ }) -> (
          (* The comatch is undegenerated when the codatatype instance's total dimension equals the intrinsic dimension.  A degenerate comatch (e.g. refl of a comatch) has a larger total dimension; displaying it as "[ … ]⁽ᵉ⁾" isn't representable as a term (Term.Act is kinetic, a comatch is potential) and a full readback of its degenerated instances is out of scope, so it falls back to the neutral's application spine ("refl r"), which is at least correct. *)
          match D.compare (TubeOf.inst tyargs) (cod_left_ins ins) with
          | Neq -> raise Comatch_fallback
          | Eq ->
              let dim = cod_left_ins ins in
              let evaldim = dim_env codata_args.env in
              (* Read back a lower field via the neutral-as-self: project the field out of the neutral, and use the neutral (a kinetic value, even though its potential value is this struct) to resolve the possibly-dependent field type. *)
              (* The return-type annotation keeps the field-map's eta ('et) polymorphic.  The higher-field branch below constrains 'et = no_eta, but only locally where it is actually reached; so a record (where 'et = has_eta and there are no higher fields) reads back its (non-leaf) tuple value through exactly the same code.  This is what lets "about (Prod A B)⁽ᵉ⁾ .trr p" display the componentwise transport rather than the stuck spine. *)
              let fields =
                Mbwd.map
                  (fun (Term.CodatafieldAbwd.Entry
                          (type i)
                          ((fld, cf) : i Field.t * (i, mode * aa * n * et) Term.Codatafield.t)) :
                       (mode * (mn * a * potential * et)) Term.StructfieldAbwd.entry ->
                    match cf with
                    | Term.Codatafield.Lower ((Adjunction { left; right; unit; _ } as adj), _, _) ->
                        (* Project the field from the neutral-as-self, keying by the adjunction unit and reading back the component behind the right-adjoint lock (all trivial for an ordinary non-modal field). *)
                        let xu = Act.act_value neutral (id_deg D.zero) unit in
                        let tyu = Act.act_ty neutral ty (id_deg D.zero) unit in
                        let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                        Term.StructfieldAbwd.Entry
                          ( fld,
                            Term.Structfield.Lower
                              ( adj,
                                plus_lock,
                                Term.Realize
                                  (readback_at lctx
                                     (field_term left xu fld (ins_zero dim))
                                     (tyof_field left (Ok xu) tyu fld ~shuf:Trivial
                                        (ins_zero evaldim))),
                                `Labeled ) )
                    | Term.Codatafield.Higher (adj, _, _, _) -> (
                        match Modalcell.compare_adjunction_id adj with
                        | Neq -> fatal (Unimplemented "displaying modal codata fields")
                        | Eq -> (
                            match Value.StructfieldAbwd.find_opt comatch_fields fld with
                            | Found (Value.Structfield.Higher (lazy hd)) -> (
                                (* "about" only reads back non-modal higher comatch fields, whose stored bodies live at the codatatype's own mode; a modal one falls back to the stored case tree. *)
                                match Modalcell.compare_adjunction_id hd.adj with
                                | Neq -> raise Comatch_fallback
                                | Eq -> (
                                    (* We handle only an undegenerated comatch (identity deg) with an empty closure environment (a top-level comatch), where the stored term can be evaluated directly in the empty environment.  A degenerate comatch (e.g. refl of a comatch) or a partially-applied one falls back to the stored case tree. *)
                                    match
                                      ( hd.env,
                                        D.compare dim (D.plus_right hd.plusdim),
                                        is_id_deg hd.deg )
                                    with
                                    | Emp _, Eq, Some _ ->
                                        let pbm =
                                          Term.PlusPbijmap.build dim (Field.dim fld)
                                            {
                                              build =
                                                (fun (type r)
                                                  (pbij : (m, i, r) pbij)
                                                  :
                                                  (r, mode * a) Term.PlusFam.t
                                                ->
                                                  match Term.PlusPbijmap.find pbij hd.terms with
                                                  | None -> raise Comatch_fallback
                                                  | Some (Term.PlusFam.PlusFam (stored_pm, term))
                                                    -> (
                                                      (* The closure environment is empty, so degenerating it leaves it empty: the stored plus-map is the proj-only one (matched below) and the stored term lives over the empty context, so it can be evaluated directly in hd.env. *)
                                                      match stored_pm with
                                                      | Suc
                                                          ( Zero (Eq Unit),
                                                            Inject (Plus_proj _),
                                                            Suc (Zero, Proj _) ) ->
                                                          let (Pbij (fldins, fldshuf)) = pbij in
                                                          let r = left_shuffle fldshuf in
                                                          let (Degctx (plusmap, dctx, denv)) =
                                                            degctx ctx r in
                                                          let ety : (mode, kinetic) value =
                                                            match D.compare_zero r with
                                                            | Zero ->
                                                                let Eq =
                                                                  eq_of_zero_shuffle fldshuf in
                                                                tyof_field (Modalcell.adj_left adj)
                                                                  (Ok neutral) ty fld ~shuf:Trivial
                                                                  fldins
                                                            | Pos _ ->
                                                                let termctx =
                                                                  Lazy.force codata_args.termctx
                                                                  <|> Anomaly
                                                                        "missing termctx for higher comatch"
                                                                in
                                                                let shuf =
                                                                  higher_codatafield_shuffleable ctx
                                                                    (length_env codata_args.env)
                                                                    termctx denv r fldshuf in
                                                                tyof_field (Modalcell.adj_left adj)
                                                                  (Ok neutral) ty fld ~shuf fldins
                                                          in
                                                          let body = eval hd.env term in
                                                          Some
                                                            (Term.PlusFam.PlusFam
                                                               (plusmap, readback_eval dctx body ety))
                                                      | _ -> raise Comatch_fallback));
                                            } in
                                        Term.StructfieldAbwd.Entry
                                          ( fld,
                                            Term.Structfield.Higher
                                              (hd.adj, plus_no_lock (Ctx.mode ctx), pbm) )
                                    | _ -> raise Comatch_fallback))
                            | _ -> raise Comatch_fallback)))
                  codata_args.fields in
              Term.Struct { eta = codata_args.eta; dim; fields; energy = Potential })
      | _ -> fatal (Anomaly "comatch readback: neutral value is not a struct"))
  | _ -> fatal (Anomaly "comatch readback: not a neutral at a codatatype")

(* Read back the *potential* value of a neutral, for the "about" command, into a display term: if it reduces (possibly under parameter abstractions) to a canonical type, a Canonical_display leaf wrapped in lambdas for the parameters; otherwise None, so the caller can fall back to displaying the stored case tree or the normal form.  The parameter abstraction is reconstructed as a real Term.Lam carrying the definition's parameter name, so e.g. "about Vec" reads back as "A ↦ data [ … : Vec A … ]".  We descend only through zero-dimensional parameter abstractions; anything else (a genuine case tree with matches/comatches, a higher-dimensional abstraction, or a stuck neutral) returns None. *)
let rec readback_about : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) Value.value -> (mode, b, potential) Term.term option =
 fun ctx value ->
  match value with
  | Neu { value = v; ty; _ } -> (
      match force_eval v with
      | Val (Value.Canonical { canonical; ins; _ }) -> (
          match canonical with
          | Data data_args ->
              let indices = Fillvec.expected_length data_args.indices in
              (* Datatypes never have a Gel dimension, so the insertion is always trivial. *)
              let Eq = eq_of_ins_zero ins in
              Some (readback_data ctx indices value data_args)
          (* Codatatypes/records are handled uniformly whether 0-dimensional, intrinsically higher (Gel-like), or degenerate. *)
          | Codata codata_args -> Some (codata_display_value ctx value codata_args)
          | UU _ | Pi _ -> None)
      | Val (Lam (xs, _, _)) -> (
          (* A function (e.g. a parameterized datatype family): apply it to a fresh parameter variable and recurse, then re-abstract.  The parameter name comes from the lambda-abstraction (the definition), not the function-type (whose binder may be anonymous). *)
          match view_type (Lazy.force ty) "readback_about" with
          | Canonical (_, Pi { x = _; filter; doms; cods }, pins, _) -> (
              let Eq = eq_of_ins_zero pins in
              let modality = Modality.filter_modality filter in
              match (D.compare_zero (CubeOf.dim doms), D.compare_zero (BindCube.dim cods)) with
              | Zero, Zero -> (
                  let argvar, argnf = dom_vars ctx modality doms in
                  let ctx =
                    Ctx.cube_vis ctx
                      (Modality.filter_idempotent filter)
                      (option_of_binder_name (top_variable xs))
                      argnf in
                  let value = apply_term value filter argvar in
                  match readback_about ctx value with
                  | None -> None
                  | Some body ->
                      Some
                        (Term.Lam
                           (singleton_variables D.zero (top_variable xs), D.zero, filter, body)))
              | _ -> None)
          | _ -> None)
      | Val (Struct _) -> (
          (* A partially-evaluated struct: a comatch, or an eta-record tuple that hasn't reduced to a leaf (e.g. the componentwise transport "(Prod A B)⁽ᵉ⁾ .trr p", which is stuck on abstract A B).  Read it back type-directed via readback_comatch, passing the neutral (whose forced value is this struct) to serve as the self-variable, so its field types resolve even though the struct itself is a non-kinetic case-tree value.  If that gives up (e.g. on a higher comatch field with a non-empty closure environment), fall back to the application spine. *)
          try Some (readback_comatch_impl ctx value (Lazy.force ty)) with Comatch_fallback -> None)
      | _ -> None)
  | _ -> None
