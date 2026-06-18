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

(* Wrapping the "Displaying" module in another module called "Readback" and opening that module allows us to refer to the module as just "Displaying" here, but exports it as "Readback.Displaying" to other files even when they open this file. *)

module Readback = struct
  module Displaying = Algaeff.Reader.Make (Bool)
end

open Readback

let () =
  Displaying.register_printer (function `Read -> Some "unhandled Readback.Displaying.read effect")

(* Reading back a comatch (the potential value of a neutral) as a display comatch requires degenerating the context for the non-projectable instances of its higher fields, and Degctx depends on Readback, so the implementation can't live here.  Instead it's a forward reference, set by a downstream module (Canonical_display).  It's invoked by "about" with the neutral (used as the self-variable) whose value is the comatch; ordinary readback never reaches it. *)
type readback_comatch_type = {
  rbc :
    'mode 'a 'z.
    ('mode, 'z, 'a) Ctx.t ->
    ('mode, kinetic) value ->
    ('mode, kinetic) value ->
    ('mode, 'a, potential) term;
}

let readback_comatch : readback_comatch_type ref =
  ref { rbc = (fun _ _ _ -> fatal (Anomaly "readback_comatch not set (load Canonical_display)")) }

let rec sort_of_ty : type mode a z.
    ?isfunc:bool -> (mode, z, a) Ctx.t -> mode View.view_type -> [ `Type | `Function | `Other ] =
 fun ?(isfunc = false) ctx -> function
  | Canonical (_, UU _, _, _) -> `Type
  | Canonical (_, Pi (_, modality, doms, cods), _, tyargs) -> (
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Neq -> fatal (Dimension_mismatch ("sort_of_ty", TubeOf.inst tyargs, CubeOf.dim doms))
      | Eq ->
          let args, newnfs = dom_vars ctx modality doms in
          let newctx = Ctx.invis ctx modality newnfs in
          let output = tyof_app cods tyargs args in
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
    ?eta:bool ->
    (mode, z, a) Ctx.t ->
    (mode, s) value ->
    (mode, kinetic) value ->
    (mode, a, s) term =
 fun ?(eta = false) ctx tm ty ->
  let view = if Displaying.read () then view_term tm else tm in
  let vty = view_type ty "readback_at" in
  match (vty, view) with
  | Canonical (_, Pi (_, modality, doms, cods), ins, tyargs), Lam (x, body) -> (
      let Eq = eq_of_ins_zero ins in
      let k = CubeOf.dim doms in
      let l = dim_binder body in
      match (D.compare (TubeOf.inst tyargs) k, D.compare k l) with
      | Neq, _ -> fatal (Dimension_mismatch ("reading back at pi 1", TubeOf.inst tyargs, k))
      | _, Neq -> fatal (Dimension_mismatch ("reading back at pi 2", k, l))
      | Eq, Eq ->
          let (Variables (m, mn, xs) as x) = View.fill_hints doms x in
          let args, newnfs = dom_vars ctx modality doms in
          let (Plus af) = N.plus (NICubeOf.out N.zero xs) in
          let newctx = Ctx.vis ctx modality m mn xs newnfs af in
          let output = tyof_app cods tyargs args in
          let body = readback_eval ~eta newctx (apply tm modality args) output in
          Term.Lam (x, modality, body))
  (* If eta-expansion is enabled, we do an eta-expanding readback of any term. *)
  | Canonical (_, Pi (name, modality, doms, cods), ins, tyargs), tm when eta ->
      let Eq = eq_of_ins_zero ins in
      let name = View.fill_hints doms name in
      let newargs, newnfs = dom_vars ctx modality doms in
      let (Any_ctx newctx) = Ctx.variables_vis ctx modality name newnfs in
      let output = tyof_app cods tyargs newargs in
      (* We carry through the eta-expansion flag so that iterated pi-types will eta-expand fully. *)
      Term.Lam (name, modality, readback_eval ~eta newctx (apply tm modality newargs) output)
  | ( Canonical
        (type mn m n)
        (( _,
           Codata
             (type c a et)
             ({ eta; opacity; fields; env = _; termctx = _; hints = _ } :
               (mode, m, n, c, a, et) codata_args),
           ins,
           _ ) :
          mode head
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
                    (fun (Value.StructfieldAbwd.Entry (fld, Value.Structfield.Lower (fldtm, l))) ->
                      Term.StructfieldAbwd.Entry
                        ( fld,
                          Term.Structfield.Lower
                            ( readback_at ctx (force_eval_term fldtm)
                                (tyof_field (Ok tm) ty fld ~shuf:Trivial fldins),
                              l ) ))
                    tmflds in
                Some (Term.Struct { eta = Eta; dim; fields; energy })
            (* In addition, if the record type is transparent, or if it's translucent and the term is a tuple in a case tree, and we are reading back for display (rather than for internal typechecking purposes), we do an eta-expanding readback. *)
            | _, `Transparent l when Displaying.read () ->
                let fields =
                  Mbwd.map
                    (fun (CodatafieldAbwd.Entry
                            (type i)
                            ((fld, Lower _) : i Field.t * (i, mode * a * n * has_eta) Codatafield.t))
                       ->
                      Term.StructfieldAbwd.Entry
                        ( fld,
                          Term.Structfield.Lower
                            ( readback_at ctx (field_term tm fld fldins)
                                (tyof_field (Ok tm) ty fld ~shuf:Trivial fldins),
                              l ) ))
                    fields in
                Some (Struct { eta = Eta; dim; fields; energy = Kinetic })
            | Neu { value; _ }, `Translucent l when Displaying.read () -> (
                match force_eval value with
                | Val (Struct _) ->
                    let fields =
                      Mbwd.map
                        (fun (CodatafieldAbwd.Entry
                                (type i)
                                ((fld, Lower _) :
                                  i Field.t * (i, mode * a * n * has_eta) Codatafield.t)) ->
                          Term.StructfieldAbwd.Entry
                            ( fld,
                              Term.Structfield.Lower
                                ( readback_at ctx (field_term tm fld fldins)
                                    (tyof_field (Ok tm) ty fld ~shuf:Trivial fldins),
                                  l ) ))
                        fields in
                    Some (Struct { eta = Eta; dim; fields; energy = Kinetic })
                | _ -> None)
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
                let ptm = act_value rtm pinv None in
                let pty = act_ty rtm ty pinv None in
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
          (* If a higher-dimensional constructor belongs to a higher version of a datatype, the instantiation arguments of the latter must be lower-dimensional versions of the same constructor.  We extract their arguments to form the boundaries of the types of the arguments of our current constructor. *)
          (* Specifically, tyargs is a tube of normals, each of which is expected to be a lower-dimensional instance of the same constructor, which therefore has a list of modal cubes as arguments.  We want to extract the top element of each of those cubes to form a tube of lists of modal values.  *)
          let tyarg_args =
            TubeOf.mmap
              {
                map =
                  (fun _ [ tm ] ->
                    match view_term tm.tm with
                    | Constr (tmname, _, tmargs) ->
                        if tmname = xconstr then
                          List.map
                            (fun (ModalValueCube.Modal (xmod, x)) ->
                              Modal (xmod, CubeOf.find_top x))
                            tmargs
                        else fatal (Anomaly "inst arg wrong constr in readback at datatype")
                    | _ -> fatal (Anomaly "inst arg not constr in readback at datatype"));
              }
              [ tyargs ] in
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

and readback_neu : type mode a z any.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (mode, z, a) Ctx.t ->
    mode head ->
    (mode, any) apps ->
    (mode, a, kinetic) term =
 fun ?(sort = (`Other, `Other)) ctx head apps ->
  match (apps, head) with
  | Emp, _ -> readback_head ~sort ctx head
  | Arg (apps, modality, args, ins), _ ->
      let (To p) = deg_of_ins ins in
      let (Locked (plus, lctx)) = Ctx.lock ctx modality in
      Term.Act
        ( App
            ( readback_neu ~sort ctx head apps,
              Modal
                ( modality,
                  plus,
                  CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf lctx tm) } [ args ] ) ),
          p,
          sort )
  | Field (apps, fld, fldplus, ins), _ ->
      let (To p) = deg_of_ins ins in
      Term.Act
        (Field (readback_neu ~sort ctx head apps, fld, id_ins (cod_left_ins ins) fldplus), p, sort)
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
      (* The source of the key is supposed to be the modal annotation of the variable, while its target is supposed to be the composite of all the locks in the context to its right.  So we remove its target from the context. *)
      let (Remove_lock (ctx, plus_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt key) in
      (* Now we look for the level variable in the remaining context. *)
      let (Lookup { result; value = _; modality; insert; plus = Plus_with_locks (c, _) }) =
        Ctx.find_level ctx level <|> No_such_level (PLevel level) in
      (* We check that (1) the modality annotating that variable is the source of the key, and (2) there are no more locks remaining to its right in the context. *)
      match (Modality.compare (Modalcell.vsrc key) modality, result, c) with
      | Eq, `Var (_, fa), Zero -> (
          (* We put the source/annotation modality back onto the context as a lock, as the "Var" term expects. *)
          let (Has_plus_lock plus_src) = plus_lock modality in
          (* If there's a nontrivial degeneracy, we act by it; otherwise we leave it off. *)
          let tm =
            match is_id_deg deg with
            | Some _ -> Term.Var (Index (insert, fa, plus_src))
            | None -> Act (Term.Var (Index (insert, fa, plus_src)), deg, sort) in
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
  | Pi (x, modality, doms, cods) ->
      let k = CubeOf.dim doms in
      let x = View.fill_hints doms x in
      let (Locked (plus, lctx)) = Ctx.lock ctx modality in
      let args, newnfs = dom_vars ctx modality doms in
      Pi
        ( x,
          Modal
            ( modality,
              plus,
              CubeOf.mmap { map = (fun _ [ dom ] -> readback_val ~sort:`Type lctx dom) } [ doms ] ),
          CodCube.build k
            {
              build =
                (fun fa ->
                  let (Any_ctx sctx) =
                    Ctx.variables_vis ctx modality (sub_variables fa x) (CubeOf.subcube fa newnfs)
                  in
                  let sargs = CubeOf.subcube fa args in
                  let (BindFam b) = BindCube.find cods fa in
                  Cod (readback_val ~sort:`Type sctx (apply_binder_term b sargs)));
            } )

and readback_at_tel : type mode n c a b ab z.
    (mode, z, c) Ctx.t ->
    (mode, n, a) env ->
    (n, mode, kinetic, unit) ModalValueCube.t list ->
    (mode, a, b, ab) Telescope.t ->
    (D.zero, n, n, (mode, kinetic) modal_value list) TubeOf.t ->
    (n, mode, c, kinetic) any_modal_term_cube list =
 fun ctx env xs tys tyargs ->
  match (xs, tys) with
  | [], Emp -> []
  | ( Modal
        (type dom modality)
        ((xmodality, x) : (dom, modality, mode) Modality.t * (n, (dom, kinetic) value) CubeOf.t)
      :: xs,
      Ext (_, Modal (tymodality, aplus, ty), tys) ) -> (
      match Modality.compare xmodality tymodality with
      | Eq ->
          let (Locked (cplus, lctx)) = Ctx.lock ctx tymodality in
          let lenv = key_env env (Modalcell.id tymodality) aplus in
          let x = CubeOf.find_top x in
          let ety = eval_term lenv ty in
          let tyargtbl = Hashtbl.create 10 in
          let [ tyarg; tms; tyargs ] =
            TubeOf.pmap
              {
                map =
                  (fun fa [ tyargs ] ->
                    match tyargs with
                    | [] -> fatal (Anomaly "missing arguments in readback_at_tel")
                    | Modal (argmod, argtm) :: argrest -> (
                        match Modality.compare argmod xmodality with
                        | Neq ->
                            fatal
                              (Modality_mismatch (`Internal, "readback_at_tel", argmod, tymodality))
                        | Eq ->
                            let fa = sface_of_tface fa in
                            let argty : (dom, kinetic) value =
                              inst
                                (eval_term (act_env lenv (op_of_sface fa)) ty)
                                (TubeOf.build D.zero
                                   (D.zero_plus (dom_sface fa))
                                   {
                                     build =
                                       (fun fb ->
                                         Hashtbl.find tyargtbl
                                           (SFace_of (comp_sface fa (sface_of_tface fb))));
                                   }) in
                            let argnorm : dom normal = { tm = argtm; ty = argty } in
                            let argtm = readback_at lctx argtm argty in
                            Hashtbl.add tyargtbl (SFace_of fa) argnorm;
                            [ argnorm; argtm; argrest ]));
              }
              [ tyargs ] (Cons (Cons (Cons Nil))) in
          let ity = inst ety tyarg in
          Modal (xmodality, cplus, TubeOf.plus_cube tms (CubeOf.singleton (readback_at lctx x ity)))
          :: readback_at_tel ctx
               (Ext
                  {
                    env;
                    plus = D.plus_zero (TubeOf.inst tyarg);
                    modality = xmodality;
                    values = `Ok (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x));
                  })
               xs tys tyargs
      | Neq -> fatal (Modality_mismatch (`Internal, "readback_at_tel", xmodality, tymodality)))
  | _ -> fatal (Anomaly "length mismatch in equal_at_tel")

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
  | Ext (envctx, entry, _) -> (
      let (Plus mk) = D.plus (dim_entry entry) in
      match entry with
      | Vis { plus_lock = dplus; bindings; _ } | Invis (dplus, bindings, _) ->
          let modality = plus_lock_modality dplus in
          let idcell = Modalcell.id modality in
          (* We are reading back bindings that were defined under a modality, so they are defined in a locked context. *)
          let (Locked (bplus, lctx)) = Ctx.lock ctx modality in
          (* We get the top entry (Now) from the environment we're reading back.  We can't just match it against Ext or LazyExt because it could have other lazy operations applied to it like Shift, Unshift, Permute, etc. *)
          let (Looked_up { act; op = Op (fc, fd); entry = xs }) =
            lookup_cube env mk modality Now (id_op (D.plus_out (dim_env env) mk)) in
          let lenv = key_env env idcell dplus in
          (* We apply the accumulated operators and keys to the entry we found. *)
          let xs = act_cube { act } (CubeOf.subcube fc xs) fd None in
          (* Now we read back all the terms and types in that environment entry.  We record the normal forms in a hashtbl as we go, to use as instantiation arguments to types of higher-dimensional terms. *)
          let xtytbl = Hashtbl.create 10 in
          let tmxs =
            CubeOf.mmap
              {
                map =
                  (fun fab [ tm ] ->
                    let (SFace_of_plus (_, fb, fa)) = sface_of_plus mk fab in
                    (* The type to read back at comes from the top entry in the codomain context.  This is a term, so we have to evaluate it to get a value before reading back at it.  We evaluate it in our given environment, so that it can use the terms to the left and also lower-dimensional terms in the current entry.  We have to lock that environment to make those latter entries available. *)
                    let ty = (CubeOf.find bindings fa).ty in
                    let ety = eval_term (act_env lenv (op_of_sface fb)) ty in
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
          let tmenv = readback_ordered_env ctx (Env.remove_top env) envctx in
          Ext (tmenv, mk, Term.Modal (modality, bplus, tmxs)))
  | Lock _ ->
      (* We remove as many locks as there are at the end of the codomain context, since keys in the environment could have composite modalities as their domain. *)
      let (Ordered_remove_locks (envctx, plus_src)) = Termctx.ordered_remove_locks envctx in
      (* Then we remove all the corresponding keys from the environment being read back, and their domain from the context we're reading back *into*. *)
      let (Remove_keys (env, cell)) = Env.remove_keys_plus_lock env plus_src in
      let (Remove_lock (ctx, plus_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt cell) in
      Key { env = readback_ordered_env ctx env envctx; cell; plus_src; plus_tgt }
  | Parametric_lock envctx -> readback_ordered_env ctx env envctx

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
  | Vis { dim; modality; plusdim; vars; bindings; hasfields; fields; fplus } ->
      let top = Binding.value (CubeOf.find_top bindings) in
      (* Fields as illusory variables are only used when typechecking records, which have substitution dimension 0 and can have no higher fields, so as field insertion we can use the identity on zero. *)
      let fins = ins_zero D.zero in
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx modality in
      let fields =
        Bwv.map
          (fun (f, x) ->
            let fldty =
              readback_val ~sort:`Type lctx (tyof_field (Ok top.tm) top.ty f ~shuf:Trivial fins)
            in
            (f, x, fldty))
          fields in
      let bindings = readback_bindings lctx bindings in
      Readback_entry (Vis { dim; plusdim; plus_lock; vars; bindings; hasfields; fields; fplus })
  | Invis (modality, bindings) ->
      (* Invisible variables are anonymous, but we can still record display hints from their types, since after readback the types are terms and the hints can no longer be computed on demand.  Since this only affects display, if anything goes wrong computing the type (e.g. the binding is an error placeholder) we just skip the hints. *)
      let hints =
        Reporter.try_with ~fatal:(fun _ -> no_hints) @@ fun () ->
        View.hints_of_ty (Binding.value (CubeOf.find_top bindings)).ty in
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx modality in
      Readback_entry (Invis (plus_lock, readback_bindings lctx bindings, hints))

let rec readback_ordered_ctx : type mode a b.
    (mode, a, b) Ctx.Ordered.t -> (mode, a, b) ordered_termctx = function
  | Emp mode -> Emp mode
  | Snoc (rest, e, af) as ctx ->
      let (Readback_entry re) = readback_entry (Ctx.of_ordered ctx) e in
      Ext (readback_ordered_ctx rest, re, af)
  | Lock (ctx, lock) -> Lock (readback_ordered_ctx ctx, lock)
  | Parametric_lock ctx -> Parametric_lock (readback_ordered_ctx ctx)

let readback_ctx : type mode a b. (mode, a, b) Ctx.t -> (mode, a, b) termctx = function
  | Permute { perm; ctx; _ } -> Permute (perm, readback_ordered_ctx ctx)

(* Build the "nontrivial shuffleable" passed to tyof_higher_codatafield when computing the type of a non-projectable instance of a higher codatatype field.  The remaining dimensions 'r have been split off, the context degenerated by them (degenv, of the degenerated ambient context), and the field's shuffle is fldshuf.  Its callbacks eval-readback values and environments to move them into the degenerated context.  This is shared between checking comatches (check_higher_field) and reading back/displaying degenerate codatatypes (Unparse). *)
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
                    let faenv = act_env degenv (op_of_sface (sface_of_tface fa)) in
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

(* ------------------------------------------------------------------------- *)
(* Reading back canonical types as display-only declarations, for "about".    *)
(* ------------------------------------------------------------------------- *)

(* The result of reading back a constructor's argument telescope from a value: the telescope as a term, plus the context and environment extended by fresh variables for its arguments (needed to read back the index values that follow it), and the (top-dimensional) values of those fresh argument variables in order (needed to build the constructor-as-a-function for degenerate datatypes). *)
type (_, _, _, _) rb_tel =
  | Rb_tel :
      ('mode, 'e, 'c, 'ec) Term.tel * ('mode, 'lev, 'ec) Ctx.t * ('mode, D.zero, 'ac) Value.env
      -> ('mode, 'e, 'c, 'ac) rb_tel

(* Read back a (zero-dimensional) telescope of value-level types into a term-level telescope in the readback context, introducing a fresh variable for each entry.  Each entry may carry a modality (constructor arguments, unlike indices, can be modal); we evaluate its type under the corresponding lock and reconstruct the modal telescope entry over the readback context, following check_tel/ext_tel. *)
let rec readback_tel : type mode lev e a c ac.
    (mode, lev, e) Ctx.t ->
    (mode, D.zero, a) Value.env ->
    (mode, a, c, ac) Term.tel ->
    (mode, e, c, ac) rb_tel =
 fun ctx env tel ->
  match tel with
  | Emp -> Rb_tel (Emp, ctx, env)
  | Ext (name, Modal (modality, plus, rty), rest) ->
      let m = dim_env env in
      let lenv = key_env env (Modalcell.id modality) plus in
      let ety = Norm.eval_term lenv rty in
      let newvars, newnfs =
        Domvars.dom_vars ctx modality
          (CubeOf.build m
             { build = (fun fa -> Norm.eval_term (act_env lenv (op_of_sface fa)) rty) }) in
      let (Locked (rplus, lctx)) = Ctx.lock ctx modality in
      let trty = readback_val ~sort:`Type lctx ety in
      let ctx = Ctx.cube_vis ctx modality name newnfs in
      let env = Value.Ext { env; plus = D.plus_zero m; modality; values = `Ok newvars } in
      let (Rb_tel (resttel, fctx, fenv)) = readback_tel ctx env rest in
      Rb_tel (Ext (name, Modal (modality, rplus, trty), resttel), fctx, fenv)

(* The result of reading back a value-level datatype constructor: its argument telescope and, for an indexed datatype, the output type (the datatype family applied to the constructor's index values). *)
type (_, _) rb_constr =
  | Rb_constr :
      ('mode, 'e, 'c, 'ec) Term.tel * ('mode, 'ec, kinetic) term option
      -> ('mode, 'e) rb_constr

(* Read back a value-level datatype constructor (at dimension zero) into the readback context: its argument telescope, and, for an indexed datatype, its output type.  The output type is the stored output term (the datatype applied to the parameters and indices) evaluated at the fresh argument variables; it is shown only for indexed datatypes (the caller passes whether the datatype is indexed), matching the convention that non-indexed constructors are displayed without an output ascription. *)
let readback_dataconstr : type mode lev e.
    (mode, lev, e) Ctx.t -> bool -> (mode, D.zero) Value.dataconstr -> (mode, e) rb_constr =
 fun ctx indexed (Dataconstr { env; args; output }) ->
  let (Rb_tel (tel, fctx, fenv)) = readback_tel ctx env args in
  let output =
    if indexed then Some (readback_val ~sort:`Type fctx (Norm.eval_term fenv output)) else None
  in
  Rb_constr (tel, output)

(* Read back the (higher-dimensional) function-type of a constructor of a *degenerate* (positive substitution dimension m) datatype.  The idea is that a constructor's type is morally a function type "(args) → out", and the type of the degenerate constructor is the degeneration of that function.  We can't take the degeneration of a constructor directly (there's no "tyof_constr"), but we *can* form the constructor-as-a-function "λ args. c args" together with its function-type "(args) → out", and then act on it by the pure degeneracy deg_zero m using act_ty.  Acting on a function-type instantiates its codomain at the faces of the function, which here are the lower-dimensional constructors, exactly producing e.g. "List⁽ᵉ⁾ (Id A) (cons. x₀ xs₀) (cons. x₁ xs₁)".  Reading back the result gives a higher-dimensional pi-type term, which unparses as "{x₀ x₁ : A} (x₂ : Id A x₀ x₁) … →⁽ᵉ⁾ …".  The constructor's output type "out" is the stored output term (e.g. "Vec A (suc. n)" for an indexed datatype, or the datatype itself for a non-indexed one) evaluated at the fresh argument variables. *)
let readback_degenerate_constr : type mode lev e m.
    (mode, lev, e) Ctx.t -> m D.t -> Constr.t -> (mode, D.zero) Value.dataconstr -> (mode, e, kinetic) term
    =
 fun _ctx _m _c _dc ->
  (* TODO(about-merge): displaying a constructor of a *degenerate* (higher-dimensional) datatype as its function-type builds a Term.Constr from modal cubes and acts on the constructor-as-a-function by a pure degeneracy; this is entangled with modal's modal-cube constructor representation and is deferred. *)
  fatal (Unimplemented "about-display of degenerate datatypes (post-modal-merge)")

(* Read back a degenerate constructor's function-type in a configuration with *no endpoints* (arity 0).  Then an m-cube has no proper faces, so we don't need the zero-dimensional base (which is unreachable anyway, as it would be a vertex of a faceless cube): we evaluate the constructor's function-type "(args) → output" directly in the degenerate (m-dimensional) environment that the constructor already carries.  There is still a (trivial, empty) instantiation, displayed as ".", so we instantiate the resulting m-dimensional function-type at the empty boundary tube before reading back.  Since the cube has no proper faces, the tube's builder is never called. *)
let readback_degenerate_constr_uninst : type mode lev e m.
    (mode, lev, e) Ctx.t -> (mode, m) Value.dataconstr -> (mode, e, kinetic) term =
 fun _ctx _dc ->
  (* TODO(about-merge): see readback_degenerate_constr; the arity-0 degenerate case is deferred too. *)
  fatal (Unimplemented "about-display of degenerate datatypes (post-modal-merge)")

(* Build the display node for a value-level (zero-dimensional) datatype: each constructor as a telescope of arguments plus, for an indexed datatype, its output type. *)
let data_display_value : type mode lev e.
    (mode, lev, e) Ctx.t ->
    bool ->
    (Constr.t, (mode, D.zero) Value.dataconstr) Abwd.t ->
    (mode, e) Term.canonical_display =
 fun ctx indexed constrs ->
  Data_display
    (Abwd.mapi
       (fun _ dc ->
         let (Rb_constr (tel, output)) = readback_dataconstr ctx indexed dc in
         Term.Tel_constr (tel, output))
       constrs)

(* Build the display node for a value-level *degenerate* (positive substitution dimension) datatype: each constructor as its (higher-dimensional) function-type.  Normally (arity ≥ 1) we obtain the underlying zero-dimensional datatype d0 as a vertex of the degenerate one (a boundary face of its degenerate-universe type) and read back each constructor's function-type via readback_degenerate_constr, which instantiates the codomain at the lower-dimensional constructors.  In a configuration with no endpoints (arity 0) the cube has no vertex, but it also has no boundary to instantiate, so we read back each constructor's function-type directly in its degenerate environment via readback_degenerate_constr_uninst. *)
let degenerate_data_display : type mode a b m j ij.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) Value.value ->
    (mode, m, j, ij) Value.data_args ->
    (mode, b) Term.canonical_display =
 fun _ctx _tm _data_args ->
  (* TODO(about-merge): see readback_degenerate_constr; whole degenerate-datatype display deferred. *)
  fatal (Unimplemented "about-display of degenerate datatypes (post-modal-merge)")
