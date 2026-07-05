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

and readback_at : type mode a z.
    ?eta:bool ->
    (mode, z, a) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, a, kinetic) term =
 fun ?(eta = false) ctx tm ty ->
  let view = if Displaying.read () then view_term tm else tm in
  let vty = view_type ty "readback_at" in
  match (vty, view) with
  | ( Canonical (_, Pi { x = _; filter; doms; cods }, ins, tyargs),
      Lam ((Variables (m, mn, xs) as x), filter2, body) ) -> (
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
          let args, newnfs = dom_vars ctx modality doms in
          let (Plus af) = N.plus (NICubeOf.out N.zero xs) in
          let newctx = Ctx.vis ctx (Modality.filter_idempotent filter) m mn xs newnfs af in
          let output = tyof_app cods tyargs filter args in
          let body = readback_at ~eta newctx (apply_term tm filter args) output in
          Term.Lam (x, n, filter, body))
  (* If eta-expansion is enabled, we do an eta-expanding readback of any term. *)
  | Canonical (_, Pi { x = name; filter; doms; cods }, ins, tyargs), tm when eta ->
      let modality = Modality.filter_modality filter in
      let Eq = eq_of_ins_zero ins in
      let newargs, newnfs = dom_vars ctx modality doms in
      let (Any_ctx newctx) = Ctx.variables_vis ctx (Modality.filter_idempotent filter) name newnfs in
      let output = tyof_app cods tyargs filter newargs in
      (* We carry through the eta-expansion flag so that iterated pi-types will eta-expand fully. *)
      Term.Lam
        ( name,
          BindCube.dim cods,
          filter,
          readback_at ~eta newctx (apply_term tm filter newargs) output )
  | ( Canonical
        (type mn m n)
        (( _,
           Codata
             (type c a et)
             ({ eta; opacity; fields; env = _; termctx = _ } : (mode, m, n, c, a, et) codata_args),
           ins,
           _ ) :
          mode head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      _ ) -> (
      match (eta, fields) with
      | Eta, (fields : (mode * a * n * has_eta) Term.CodatafieldAbwd.t) -> (
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
          match is_id_ins ins with
          | Some _ -> (
              match readback_at_record tm ty with
              | Some res -> res
              | None -> readback_val_sorted ctx tm vty)
          | None -> (
              (* A nontrivially permuted record is not a record type, but we can permute its arguments to find elements of a record type that we can then eta-expand and re-permute. *)
              let (Perm_to p) = perm_of_ins ins in
              let pinv = deg_of_perm (perm_inv p) in
              let ptm = act_value tm pinv None in
              let pty = act_ty tm ty pinv None in
              match readback_at_record ptm pty with
              | Some res -> Act (res, deg_of_perm p, (`Other, `Other))
              | None -> readback_val_sorted ctx tm vty))
      | Noeta, _ -> readback_val_sorted ctx tm vty)
  | Canonical (_, Data { constrs; _ }, ins, tyargs), Constr (xconstr, xn, xargs) -> (
      let Eq = eq_of_ins_zero ins in
      (* Pick out the constructor of the datatype that matches the one we're reading back *)
      let (Dataconstr { env; args = argtys; indices = _ }) =
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

and readback_val_sorted : type mode a z.
    (mode, z, a) Ctx.t -> (mode, kinetic) value -> mode View.view_type -> (mode, a, kinetic) term =
 fun ctx tm vty ->
  let sort = sort_of_ty ctx vty in
  readback_val ~sort ctx tm

and readback_val : type mode a z.
    ?sort:[ `Type | `Function | `Other ] ->
    (mode, z, a) Ctx.t ->
    (mode, kinetic) value ->
    (mode, a, kinetic) term =
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

and readback_neu : type mode a z any.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (mode, z, a) Ctx.t ->
    mode head ->
    (mode, any) apps ->
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
      let (Lookup { result; value = _; modality; filter; insert; plus = Plus_with_locks (c, _) }) =
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
          let lenv = key_env env (Modalcell.id tymodality) aplus in
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
          let (Looked_up { act; op; entry = xs }) =
            lookup_cube aenv m_k modality Now (id_opt_op mk) in
          (* As usual, the missing endpoints in sface_of_filter should be canceled by degeneracies in the non-unary case. *)
          let (Op (fc, fd)) =
            op_of_opt op <|> Anomaly "unexpected missing endpoint in readback_ordered_env" in
          (* We are reading back bindings that were defined under a modality, so they are defined in a locked context. *)
          let (Locked (bplus, lctx)) = Ctx.lock ctx modality in
          (* We also analogously key the environment we're reading back, for purposes of evaluating types. *)
          let lenv = key_env aenv (Modalcell.id modality) dplus in
          (* We apply the accumulated operators and keys to the entry we found. *)
          let xs = act_cube { act } (CubeOf.subcube fc xs) fd None in
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
      let (Ordered_remove_locks (envctx, plus_src)) = Termctx.ordered_remove_locks envctx in
      (* Then we remove all the corresponding keys from the environment being read back, and their domain from the context we're reading back *into*. *)
      let (Restrict_keys (env, cell, pre)) = restrict_keys_plus_lock env plus_src in
      let (Remove_lock (ctx, plus_tgt)) = Ctx.remove_lock ctx (Modalcell.vtgt cell) in
      (* We read back the residual environment as a keyed term environment, and wrap it in a prekey carrying the accumulated prekey action, dropping the latter if it is an identity (as when no prekeys were present). *)
      let keyed = Term.Key { env = readback_ordered_env ctx env envctx; cell; plus_src; plus_tgt } in
      match Modalcell.compare_id pre with
      | Eq -> keyed
      | Neq -> Prekey (keyed, pre))
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
              readback_val ~sort:`Type lctx (tyof_field (Ok top.tm) top.ty f ~shuf:Trivial fins)
            in
            (f, x, fldty))
          fields in
      let bindings = readback_bindings lctx bindings in
      Readback_entry
        (Vis { dim; plusdim; plus_lock; vars; bindings; hasfields; fields; fplus; filter })
  | Invis { filter; bindings } ->
      let modality = Modality.filter_modality filter in
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx modality in
      Readback_entry (Invis { plus_lock; filter; bindings = readback_bindings lctx bindings })

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
