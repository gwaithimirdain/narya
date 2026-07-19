open Bwd
open Util
open Modal
open Tbwd
open Reporter
open Dim
open Tctx
open Term
open Value
open Act
open Printable
open View

(* Since some entries in an environment are lazy and some aren't, lookup_cube returns a cube whose entries belong to an existential type, along with a function to act on any element of that type and force it into a value.  It also returns an accumulated operator by which to act, first selecting an entry in the cube with a face and then acting on that value by a degeneracy.  Finally, it also returns an accumulated modal key substitution. *)
type (_, _) looked_up_cube =
  | Looked_up : {
      act :
        'x 'y 'mu 'nu 'cod.
        'a -> ('x, 'y) deg -> ('mode, 'mu, 'nu, 'cod) Modalcell.t -> ('mode, kinetic) value;
      op : ('m, 'n) opt_op;
      entry : ('n, 'a) CubeOf.t;
      (* The accumulated action of any prekeys encountered on the way to the variable, transported to the mode of the looked-up value.  It is an identity cell if there were none. *)
      pre : ('mode, 'pmu, 'pnu, 'pcod) Modalcell.t;
    }
      -> ('mode, 'm) looked_up_cube

(* Require that the supplied list contains exactly one argument for each annotated variable being added, and add all of those cubes to the given environment. *)
let rec take_args : type dom window mode annotations m n k kn a b ab.
    (mode, m, a) env ->
    (k, n, kn) D.plus ->
    (kn, dom, kinetic) modal_value_cube list ->
    (dom, window, mode) Modality.t ->
    (dom, window, mode, k, m) Modality.filter_dim ->
    (n, mode, annotations, mode, mode, b, mode) VarAnnotate.fwd_t ->
    (mode, b, mode, a, unit, ab) Tctx.bcomp ->
    (mode, m, ab) env =
 fun env k_n dargs window_modality filter_window_k_m annotate comp ->
  match (dargs, annotate, comp) with
  | [], Zero _, Zero -> env
  | ( Modal
        (type mdom mmod pq)
        ((filter_constr_pq_kn, arg) : (mdom, mmod, dom, pq, kn) Modality.filter_dim * _)
      :: args,
      Suc (Annotate filter_window_constr_q_n, annotate),
      Suc (Dim _, comp) ) -> (
      (* The value's stored filter is that of its constructor annotation mu, whose codomain is the (inner) mode of the datatype, while the context annotation is the composite of the window modality with mu, whose codomain is the outer mode.  So we compose mu with the window before comparing. *)
      let _m = dim_env env in
      let _k = Modality.filtered _m filter_window_k_m in
      let n = D.plus_right k_n in
      let (Has_filter filter_window_n_n) = Modality.filter window_modality n in
      match D.compare (Modality.filtered n filter_window_n_n) n with
      | Neq -> fatal (Unimplemented "filtering window modalities for higher-dimensional matches")
      | Eq -> (
          let constr_modality = Modality.filter_modality filter_constr_pq_kn in
          let (Comp window_constr_comp) = Modality.comp constr_modality in
          let window_constr_modality = Modality.comp_out window_modality window_constr_comp in
          let window_constr_modality' = Modality.filter_modality filter_window_constr_q_n in
          match Modality.compare window_constr_modality window_constr_modality' with
          | Neq ->
              fatal
                (Modality_mismatch
                   (`Internal, "take_args", window_constr_modality, window_constr_modality'))
          | Eq ->
              let (Filter_of_plus (p_q, filter_constr_p_k, filter_constr_q_n)) =
                Modality.filter_of_plus k_n filter_constr_pq_kn in
              let filter_window_constr_p_m =
                Modality.filter_comp window_constr_comp filter_window_k_m filter_constr_p_k in
              let filter_window_constr_q_n' =
                Modality.filter_comp window_constr_comp filter_window_n_n filter_constr_q_n in
              let Eq = Modality.filter_uniq filter_window_constr_q_n filter_window_constr_q_n' in
              let env =
                Ext
                  {
                    env;
                    plus = p_q;
                    filter = filter_window_constr_p_m;
                    filtered = Modality.filter_idempotent filter_window_constr_q_n;
                    values = `Ok arg;
                  } in
              take_args env k_n args window_modality filter_window_k_m annotate comp))
  | _ -> fatal (Anomaly "wrong number of arguments in argument list")

(* The adjunction of a (lower) field of a record type, together with the non-keyed type of its component: the type at which the component of a tuple is checked or read back, living behind the lock by the right adjoint. *)
type _ tyof_modal_field =
  | Tyof_modal_field :
      ('amode, 'f, 'g, 'gmode) Modalcell.adjunction * ('gmode, kinetic) value
      -> 'amode tyof_modal_field

(* Eval-readback callback for tyof_higher_codatafield *)
type (_, _, _, _, _) shuffleable =
  | Trivial : ('mode, D.zero, 'i, 'i, 'c) shuffleable
  | Nontrivial : {
      dbwd : ('mode, 'c) Tctx.t;
      shuffle : ('r, 'h, 'i) shuffle;
      deg_env :
        's 'sh 'r_sh.
        ('s, 'h, 'sh) D.plus ->
        ('r, 'sh, 'r_sh) D.plus ->
        ('mode, 'sh, ('c, ('mode id, D.zero) dim_entry) snoc) env ->
        ('mode, 'r_sh, ('c, ('mode id, D.zero) dim_entry) snoc) env;
      deg_nf : 'mode normal -> 'mode normal;
    }
      -> ('mode, 'r, 'h, 'i, 'c) shuffleable

let rec view_term : type mode s. (mode, s) value -> (mode, s) value =
 fun tm ->
  if GluedEval.read () then
    match tm with
    | Neu { value; ty; _ } -> (
        (* For glued evaluation, when viewing a term, we force its value and proceed to view that value instead. *)
        match force_eval value with
        | Realize v -> view_term v
        | Val (Canonical { canonical = Data d; _ }) when Option.is_none !(d.tyfam) ->
            d.tyfam := Some (lazy { tm; ty = Lazy.force ty });
            tm
        | _ -> tm)
    | _ -> tm
  else tm

(* Viewing a type fails if the argument is not fully instantiated.  In most situations this would be a bug, but we allow the caller to specify it differently, since during typechecking it could be a user error. *)
and view_type : type mode.
    ?severity:Asai.Diagnostic.severity -> (mode, kinetic) value -> string -> mode view_type =
 fun ?(severity = Asai.Diagnostic.Bug) (ty : (mode, kinetic) value) (err : string) :
     mode view_type ->
  match ty with
  | Neu { head; args; value; ty = _ } -> (
      (* Glued evaluation: when viewing a type, we force its value and proceed to view that value instead. *)
      match force_eval value with
      | Val (Canonical { mode; canonical = c; tyargs; ins; fields = _; inst_fields = _ }) -> (
          (match c with
          | Data d when Option.is_none !(d.tyfam) ->
              d.tyfam :=
                Some (lazy { tm = ty; ty = inst (universe mode (TubeOf.inst tyargs)) tyargs })
          | _ -> ());
          match D.compare_zero (TubeOf.uninst tyargs) with
          | Zero ->
              let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (TubeOf.inst tyargs)) in
              Canonical (head, c, ins, tyargs)
          | Pos k -> fatal ~severity (Type_not_fully_instantiated (err, k)))
      | Realize v -> view_type ~severity v err
      | _ -> (
          match inst_of_apps args with
          | apps, Some (Any_tube tyargs) -> (
              match D.compare_zero (TubeOf.uninst tyargs) with
              | Pos k -> fatal ~severity (Type_not_fully_instantiated (err, k))
              | Zero ->
                  let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (TubeOf.inst tyargs)) in
                  Neutral (head, apps, tyargs))
          | apps, None -> Neutral (head, apps, TubeOf.empty D.zero)))
  | _ -> fatal ~severity (Type_expected (err, Dump.Val ty))

(* Evaluation of terms and evaluation of case trees are technically separate things.  In particular, evaluating a kinetic (standard) term always produces just a value, whereas evaluating a potential term (a function case tree) can either

   1. Produce a new partially-evaluated case tree that isn't fully applied yet.  This is actually represented by a value that's either a Lam or a Struct.
   2. Reach a leaf and produce a value.
   3. Conclude that the case tree is true neutral and will never reduce further.

   These possibilities are encoded in an "evaluation", defined in Syntax.Value.  The point is that, just as with the representation of terms, there is enough commonality between the two (application of lambdas and field projection from structs) that we don't want to duplicate the code, so we define the evaluation functions to return an "evaluation" result that is a GADT parametrized by the kind of energy of the term. *)

(* The master evaluation function. *)
and eval : type mode m b s. (mode, m, b) env -> (mode, b, s) term -> (mode, s) evaluation =
 fun env tm ->
  match tm with
  | Var v -> Val (lookup env v)
  | Const name -> (
      let dim = dim_env env in
      let (Definition { mode; ty = cty; tm = defn; parametric = _ }) = Global.find name in
      match Mode.compare mode (mode_env env) with
      | Eq -> (
          (* Its type must also be instantiated at the lower-dimensional versions of itself. *)
          let ty =
            lazy
              (inst
                 (eval_term (Emp (mode, dim)) cty)
                 (TubeOf.build D.zero (D.zero_plus dim)
                    {
                      build =
                        (fun fa ->
                          (* To compute those lower-dimensional versions, we recursively evaluate the same constant in lower-dimensional contexts. *)
                          let tm =
                            eval_term
                              (act_env env (opt_op_of_sface (sface_of_tface fa)))
                              (Const name) in
                          (* We need to know the type of each lower-dimensional version in order to annotate it as a "normal" instantiation argument.  But we already computed that type while evaluating the term itself, since as a neutral term it had to be annotated with its type. *)
                          match tm with
                          | Neu { ty = (lazy ty); _ } -> { tm; ty }
                          | _ -> fatal (Anomaly "eval of lower-dim constant not neutral/canonical"));
                    })) in
          let head = Const { name; ins = ins_zero dim } in
          match defn with
          | `Defined tree -> (
              if GluedEval.read () then
                (* Glued evaluation: we evaluate the definition lazily and return a neutral with that lazy evaluation stored. *)
                Val (Neu { head; args = Emp; value = lazy_eval (Emp (mode, dim)) tree; ty })
              else
                let value = eval (Emp (mode, dim)) tree in
                let newtm = Neu { head; args = Emp; value = ready value; ty } in
                match value with
                | Realize x -> Val x
                | Val (Canonical { canonical = Data d; _ }) ->
                    if Option.is_none !(d.tyfam) then
                      d.tyfam := Some (lazy { tm = newtm; ty = Lazy.force ty });
                    Val newtm
                | _ -> Val newtm)
          | `Axiom -> Val (Neu { head; args = Emp; value = ready Unrealized; ty }))
      | Neq -> fatal (Mode_mismatch (`Internal, "evaluating a constant", mode, None, mode_env env)))
  | Meta (meta, ambient) -> (
      let dim = dim_env env in
      let head = Value.Meta { meta; env; ins = ins_zero dim } in
      (* As with constants, we need to instantiate the type at the same meta evaluated at lower dimensions. *)
      let make_ty meta ty =
        inst (eval_term env ty)
          (TubeOf.build D.zero (D.zero_plus dim)
             {
               build =
                 (fun fa ->
                   let tm =
                     eval_term
                       (act_env env (opt_op_of_sface (sface_of_tface fa)))
                       (Meta (meta, Kinetic)) in
                   match tm with
                   | Neu { ty = (lazy ty); _ } -> { tm; ty }
                   | _ -> fatal (Anomaly "eval of lower-dim meta not neutral/canonical"));
             }) in
      match (Global.find_meta meta, ambient) with
      (* If a metavariable has a definition that fits with the current energy, we simply evaluate that definition. *)
      | { tm = `Defined tm; energy = Potential; _ }, Potential -> eval env tm
      | { tm = `Defined tm; energy = Kinetic; _ }, Kinetic -> eval env tm
      | { tm = `Defined tm; energy = Kinetic; _ }, Potential -> Realize (eval_term env tm)
      | { tm = `Defined tm; energy = Potential; ty; _ }, Kinetic -> (
          if GluedEval.read () then
            (* A defined potential metavariable in kinetic context evaluates to a glued neutral, with its evaluated definition stored lazily. *)
            Val (Neu { head; args = Emp; value = lazy_eval env tm; ty = lazy (make_ty meta ty) })
          else
            (* If a potential metavariable with a definition is used in a kinetic context, and doesn't evaluate yet to a kinetic result, we again have to build a neutral. *)
            match eval env tm with
            | Realize tm -> Val tm
            | value ->
                Val (Neu { head; args = Emp; value = ready value; ty = lazy (make_ty meta ty) }))
      (* If an undefined potential metavariable appears in a case tree, then that branch of the case tree is stuck.  We don't need to return the metavariable itself; it suffices to know that that branch of the case tree is stuck, as the constant whose definition it is should handle all identity/equality checks correctly. *)
      | _, Potential -> Unrealized
      (* To evaluate an undefined kinetic metavariable, we have to build a neutral. *)
      | { ty; _ }, Kinetic ->
          Val (Neu { head; args = Emp; value = ready Unrealized; ty = lazy (make_ty meta ty) }))
  | MetaEnv (meta, metaenv) ->
      let (Plus m_n) = D.plus (dim_term_env metaenv) in
      eval (eval_env env m_n metaenv) (Term.Meta (meta, Kinetic))
  | UU (mode, n) ->
      let m = dim_env env in
      let (Plus mn) = D.plus n in
      Val (universe mode (D.plus_out m mn))
  | Inst (tm, args) -> (
      (* The arguments are an (n,k) tube, with k dimensions instantiated and n dimensions uninstantiated. *)
      let n = TubeOf.uninst args in
      let k = TubeOf.inst args in
      let n_k = TubeOf.plus args in
      (* Add the environment dimension to the uninstantiated dimensions *)
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      (* Evaluate the inner term.  This gives an m+n+k dimensional object; it might have been instantiated from something higher-dimensional, but requires a full m+n+k tube to become fully instantiated.  We will instantiate k of those dimensions, leaving m+n. *)
      let newtm = eval_term env tm in
      let (Plus mn_k) = D.plus k in
      let mnk = D.plus_out mn mn_k in
      (* tys is a complete m+n+k tube, giving the types of all the arguments that newtm remains to be instantiated by. *)
      let (Full_tube tys) = inst_tys newtm in
      match D.compare (TubeOf.inst tys) mnk with
      | Neq -> fatal (Dimension_mismatch ("evaluation instantiation", TubeOf.inst tys, mnk))
      | Eq ->
          (* used_tys is an (m+n,k) tube, with m+n uninstantiated and k instantiated.  These are the types that we must instantiate to give the types of the added instantiation arguments. *)
          let used_tys = TubeOf.pboundary (D.zero_plus mn) mn_k tys in
          let newargstbl = Hashtbl.create 10 in
          let newargs =
            TubeOf.mmap
              {
                map =
                  (fun fa [ ty ] ->
                    (* fa : p+q => m+n+k, fa = fb+fc where fb : p => m and fcd : q => n+k. *)
                    let (TFace_of_plus (_, fb, fcd)) = tface_of_plus m_n fa in
                    let fa = sface_of_tface fa in
                    let Eq = D.plus_uniq (cod_plus_of_tface fcd) n_k in
                    (* Thus tm is p+q dimensional. *)
                    let tm = eval_term (act_env env (opt_op_of_sface fb)) (TubeOf.find args fcd) in
                    (* So its type needs to be fully instantiated at that dimension. *)
                    let ty =
                      inst ty
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fa))
                           {
                             build =
                               (fun fij ->
                                 let faij = comp_sface fa (sface_of_tface fij) in
                                 Hashtbl.find newargstbl (SFace_of faij));
                           }) in
                    let v = { tm; ty } in
                    Hashtbl.add newargstbl (SFace_of fa) v;
                    v);
              }
              [ used_tys ] in
          (* The types not in used_tys form a complete m+n tube, which will be the remaining instantiation arguments of the type of the result.  We don't need to worry about that here, it's taken care of in "inst". *)
          Val (inst newtm newargs))
  | Lam (Variables (n, n_k, vars), p, filter, body) ->
      let m = dim_env env in
      let modality = Modality.filter_modality filter in
      let (Has_filter filter_lm) = Modality.filter modality m in
      let l = Modality.filtered m filter_lm in
      let (Plus l_nk) = D.plus (D.plus_out n n_k) in
      let (Plus m_p) = D.plus p in
      let (Plus l_n) = D.plus n in
      let ln_k = D.plus_assocl l_n n_k l_nk in
      Val
        (Lam
           ( Variables (D.plus_out l l_n, ln_k, vars),
             Modality.filter_plus l_nk m_p filter_lm filter,
             eval_binder env m_p modality filter body ))
  | App (fn, k, filter_nk, Modal (modality, al, args)) ->
      (* First we evaluate the function. *)
      let efn = eval_term env fn in
      (* The environment is m-dimensional and the original application is n-dimensional, so the *substituted* application is m+n dimensional.  However, the stored cube of arguments is at the *filtered* dimension of the original application, and likewise the arguments of the substituted application must be at *its* filtered dimension, which is (filtered m)+n.  So, as in the Constr case below, we filter the dimension m of the environment by the modality, acting on the environment by a face to cut it down to the filtered dimension. *)
      let m = dim_env env in
      let n = CubeOf.dim args in
      let (Has_filter filter_lm) = Modality.filter modality m in
      let l = Modality.filtered m filter_lm in
      let (Plus l_n) = D.plus n in
      let ln = D.plus_out l l_n in
      (* Then we evaluate all the arguments, not just in the (filtered, keyed) environment, but in that environment acted on by all the strict faces of l.  Since the given arguments are indexed by strict faces of n, the result is a collection of values indexed by strict faces of l+n.  *)
      let lenv = key_id_env env al in
      let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter m filter_lm)) in
      let eargs = eval_args flenv l_n ln args in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      let (Plus m_k) = D.plus k in
      let filter_total = Modality.filter_plus l_n m_k filter_lm filter_nk in
      apply efn filter_total eargs
  | Field (Modal (fm, plus_lock, tm), fld, fldins) -> (
      let m = dim_env env in
      let n, l = (dom_ins fldins, cod_left_ins fldins) in
      match Modality.compare_id fm with
      | Eq ->
          (* An ordinary field (identity adjunction), including all higher fields, does no dimension filtering: the term being projected lives behind a (trivial) lock by the identity, evaluated in the environment keyed by the identity cell. *)
          let Plus m_n, Plus m_l = (D.plus n, D.plus l) in
          let ltm = eval_term (key_id_env env plus_lock) tm in
          field fm ltm fld (plus_ins m m_n m_l fldins)
      | Neq ->
          (* A genuinely modal field over a (possibly nonparametric) left adjoint fm.  The term being projected lives behind a lock by fm, hence at the dimension m filtered by fm; we evaluate it in the keyed, locked environment cut down to that filtered dimension k by a face.  We then project at dimension k and degenerate the result back up to the outer dimension m.  For a nonparametric fm at a dimension it filters nontrivially, the field "disappears": k < m, so this projection is genuinely a degeneracy of a lower-dimensional one.  (For a lower field, cod_left_ins fldins = 0, so k is the whole result dimension.) *)
          let (Has_filter kfilter) = Modality.filter fm m in
          let k = Modality.filtered m kfilter in
          let (Plus k_n) = D.plus n in
          let (Plus k_l) = D.plus l in
          let lenv = key_id_env env plus_lock in
          let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter m kfilter)) in
          let ltm = eval_term flenv tm in
          let proj = field fm ltm fld (plus_ins k k_n k_l fldins) in
          act_evaluation proj (Modality.deg_of_filter m kfilter) (Modalcell.id2 (Modality.tgt fm)))
  | Struct { eta; dim = n; fields; energy } ->
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let ins = ins_zero mn in
      let fields = eval_structfield_abwd env m m_n mn fields in
      Val (Struct { fields; ins; energy; eta })
  | Constr (type n) ((constr, n, args) : _ * n D.t * _) ->
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let eargs =
        List.map
          (fun (Term.Modal (lfilter, al, tm)) ->
            let modality = Modality.filter_modality lfilter in
            let (Has_filter kfilter) = Modality.filter modality m in
            let k = Modality.filtered m kfilter in
            let (Plus k_l) = D.plus (Modality.filtered n lfilter) in
            let kl = D.plus_out k k_l in
            let filter = Modality.filter_plus k_l m_n kfilter lfilter in
            let lenv = key_id_env env al in
            (* The dimension of the cube of arguments that we want should be filtered by the modality.  Thus, we need to filter the dimension of the environment we evaluate it in as well.  We do this by acting with a face: in the unary case this is the unique such face, in other cases it is a dummy face.  The mode theory used for the non-unary cases (the nonparametric modality is only a comonad) should ensure that the dummy endpoints in the non-unary case never actually get used; they should be canceled out by degeneracies. *)
            let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter m kfilter)) in
            Value.Modal (filter, eval_args flenv k_l kl tm))
          args in
      Val (Constr (constr, mn, eargs))
  | Pi
      (type l n dom modality)
      ({ x; filter = lfilter; doms; cods } : (l, n, dom, modality, mode, b) Term.pi_args) ->
      let (Term.Modal (modality, al, doms)) = doms in
      (* We are starting with an n-dimensional pi-type and evaluating it in an m-dimensional environment, producing an (m+n)-dimensional result.  The domains of the given pi-type filter the dimension n to l. *)
      let l, n = (CubeOf.dim doms, CodCube.dim cods) in
      let m = dim_env env in
      (* We filter the dimension m by the modality to get k, and that is what gets added to the dimension of the domains. *)
      let (Has_filter (type k) (kfilter : (dom, modality, mode, k, m) Modality.filter_dim)) =
        Modality.filter modality m in
      let k = Modality.filtered m kfilter in
      let (Plus (type kl) (k_l : (k, l, kl) D.plus)) = D.plus l in
      let kl = D.plus_out k k_l in
      let (Plus (type mn) (m_n : (m, n, mn) D.plus)) = D.plus n in
      let mn = D.plus_out m m_n in
      let filter = Modality.filter_plus k_l m_n kfilter lfilter in
      (* The basic thing we do is evaluate the cubes of domains and codomains. *)
      let lenv = key_id_env env al in
      let doms =
        CubeOf.build kl
          {
            build =
              (fun fab ->
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus k_l fab in
                (* Again, we have to act by a face to get the environment dimension down to k. *)
                let op =
                  comp_opt_op
                    (opt_op_of_opt_sface (Modality.sface_of_filter m kfilter))
                    (opt_op_of_sface fa) in
                eval_term (act_env lenv op) (CubeOf.find doms fb));
          } in
      let cods =
        BindCube.build mn
          {
            build =
              (fun fab ->
                let (SFace_of_plus (i_j, fa, fb)) = sface_of_plus m_n fab in
                let (Filter_sface (_, jfilter1)) = Modality.filter_sface lfilter fb in
                let (Cod (jfilter2, x)) = CodCube.find cods fb in
                let Eq = Modality.filter_uniq jfilter1 jfilter2 in
                BindFam (eval_binder (act_env env (opt_op_of_sface fa)) i_j modality jfilter1 x));
          } in
      (* However, because the result will be a Neu, we need to know its type as well.  The starting n-dimensional pi-type (which is itself uninstantiated) lies in a full instantiation of the n-dimensional universe at lower-dimensional pi-types formed from subcubes of its domains and codomains.  Accordingly, the resulting (m+n)-dimensional pi-type will like in a full instantiation of the (m+n)-dimensional universe at lower-dimensional pi-types obtained by evaluating these at appropriately split faces.  Since each of them *also* belongs to a universe instantiated similarly, and needs to know its type not just because it is an uninst but because it is a normal, we build the whole cube at once and then take its top. *)
      let pitbl = Hashtbl.create 10 in
      (* Since we only care about the hashtbl and the top, and we can get that from the hashtbl at the end anyway, we don't bother actually putting the normals into a meaningful cube. *)
      let build : type u. (u, mn) sface -> unit =
       fun fab ->
        let kl = dom_sface fab in
        let codmode = mode_env env in
        let ty =
          inst (universe codmode kl)
            (TubeOf.build D.zero (D.zero_plus kl)
               {
                 build =
                   (fun fc -> Hashtbl.find pitbl (SFace_of (comp_sface fab (sface_of_tface fc))));
               }) in
        let (Filter_sface (fab', ufilter)) = Modality.filter_sface filter fab in
        let (SFace_of_plus (ab, fa', fb')) = sface_of_plus k_l fab' in
        let subdoms, subcods = (CubeOf.subcube fab' doms, BindCube.subcube fab cods) in
        let subx = plus_variables (dom_sface fa') ab (sub_variables fb' x) in
        let head : mode head = Pi { x = subx; filter = ufilter; doms = subdoms; cods = subcods } in
        (* We don't need fibrancy fields for all the boundary types, since once something "is a type" we don't need it to be in Fib any more. *)
        let fields : (mode * u * potential * no_eta) Value.StructfieldAbwd.t =
          match (is_id_sface fab, Fibrancy.PiValuesMap.find_opt modality !Fibrancy.pi) with
          | None, _ | _, None -> Bwd.Emp
          | Some Eq, Some fields ->
              (* For the top face, we compute its fibrancy fields by evaluating the generic "fibrancy fields of a pi" at the evaluated domains and codomains.  *)
              let values =
                let build : type ij. (ij, mn) sface -> (mode, kinetic) value =
                 fun fa ->
                  let (BindFam b) = BindCube.find cods fa in
                  let (Filter_sface (fa', filter')) = Modality.filter_sface filter fa in
                  Lam (sub_variables fa' (plus_variables k k_l x), filter', b) in
                `Ok (CubeOf.build (BindCube.dim cods) { build }) in
              let pi_env =
                Ext
                  {
                    env =
                      Ext
                        {
                          env = Emp (codmode, mn);
                          plus = D.plus_zero (D.plus_out k k_l);
                          filter;
                          filtered = Modality.filter_zero modality;
                          values = `Ok doms;
                        };
                    plus = D.plus_zero mn;
                    filter = Modality.filter_id codmode mn;
                    filtered = Modality.filter_zero (Modality.id codmode);
                    values;
                  } in
              eval_structfield_abwd pi_env mn (D.plus_zero mn) mn fields in
        let value =
          ready
            (Val
               (Canonical
                  {
                    mode = mode_env env;
                    canonical = Pi { x = subx; filter = ufilter; doms = subdoms; cods = subcods };
                    tyargs = TubeOf.empty kl;
                    ins = ins_zero kl;
                    fields;
                    inst_fields = Some fields;
                  })) in
        let tm = Neu { head; args = Emp; value; ty = Lazy.from_val ty } in
        Hashtbl.add pitbl (SFace_of fab) { tm; ty } in
      let _ = CubeOf.build mn { build } in
      Val (Hashtbl.find pitbl (SFace_of (id_sface mn))).tm
  | Let (_, Modal (modality, al, v), body) ->
      (* We evaluate let-bindings lazily, on the chance they aren't actually used. *)
      let m = dim_env env in
      let (Has_filter fm) = Modality.filter modality m in
      let k = Modality.filtered m fm in
      let lenv = key_id_env env al in
      let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter m fm)) in
      eval
        (Ext
           {
             env;
             plus = D.plus_zero k;
             filter = fm;
             filtered = Modality.filter_zero modality;
             values =
               `Lazy
                 (CubeOf.build k
                    { build = (fun fa -> lazy_eval (act_env flenv (opt_op_of_sface fa)) v) });
           })
        body
  (* It's tempting to write just "act_value (eval env x) s" here, but that is WRONG!  Pushing a substitution through an operator action requires whiskering the operator by the dimension of the substitution. *)
  | Act (x, s, _) ->
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg s) in
      let (Plus kn) = D.plus (cod_deg s) in
      let ks = plus_deg k kn km s in
      (* We push as much of the resulting degeneracy into the environment as possible, in hopes that the remaining insertion outside will be trivial and act_value will be able to short-circuit.  (Ideally, the insertion would be carried through by eval for a single traversal in all cases.) *)
      let (Insfact (is, ins)) = insfact ks kn in
      let (To p) = deg_of_ins ins in
      Val
        (act_value (eval_term (act_env env (opt_op_of_deg is)) x) p (Modalcell.id2 (mode_env env)))
  | Key { tm; cell; plus_src; plus_tgt } ->
      (* To evaluate a key, we strip off the part of the environment corresponding to the codomain of the key cell, then compose the keys we found there with the supplied key to make a new key on an environment for evaluating the body.  The resulting environment is back at the original mode, so any prekey action stripped along the way is re-applied as a prekey on top. *)
      let (Restrict_keys (env, extra, mu12, keys, pre)) = restrict_keys env plus_tgt in
      let (Comp nu12) = Modality.comp (Modalcell.vsrc cell) in
      let extra_cell = Modalcell.postwhisker nu12 mu12 (plus_lock_modality extra) cell in
      let env = key_env env (Modalcell.vcomp keys extra_cell) (plus_lock_comp extra plus_src nu12) in
      let env = prekey_env env pre in
      eval env tm
  | Match { tm; window; plus_lock; dim = match_dim; branches } -> (
      let env_dim = dim_env env in
      let kenv = key_id_env env plus_lock in
      let (Has_filter fw) = Modality.filter window env_dim in
      let akenv = act_env kenv (opt_op_of_opt_sface (Modality.sface_of_filter env_dim fw)) in
      let (Plus plus_dim) = D.plus match_dim in
      (* Get the argument being inspected *)
      match view_term (eval_term akenv tm) with
      (* To reduce nontrivially, the discriminee must be an application of a constructor. *)
      | Constr (name, constr_dim, dargs) -> (
          match Constr.Map.find_opt name branches with
          (* Matches are constructed to contain all the constructors of the datatype being matched on, and this constructor belongs to that datatype, so it ought to be in the match. *)
          | None ->
              fatal
                (Anomaly
                   (Printf.sprintf "constructor %s missing from compiled match"
                      (Constr.to_string name)))
          | Some (Branch { annotate; comp; perm; tm }) -> (
              let total_dim = D.plus_out (Modality.filtered env_dim fw) plus_dim in
              match D.compare constr_dim total_dim with
              | Neq -> fatal (Dimension_mismatch ("evaluating match", constr_dim, total_dim))
              | Eq ->
                  (* If we have a branch with a matching constructor, then our constructor must be applied to exactly the right number of elements (in dargs).  In that case, we pick them out and add them to the environment. *)
                  let env = take_args env plus_dim dargs window fw annotate comp in
                  (* Then we proceed recursively with the body of that branch. *)
                  eval (Permute (perm, env)) tm)
          (* If this constructor belongs to a refuted case, it must be that we are in an inconsistent context with some neutral belonging to an empty type.  In that case, the match must be stuck. *)
          | Some Refute -> Unrealized)
      (* Otherwise, the case tree doesn't reduce. *)
      | _ -> Unrealized)
  | Realize tm -> Realize (eval_term env tm)
  | Canonical c -> eval_canonical env c
  | Unshift (n, plusmap, tm) ->
      let (Cofactor mn) =
        D.cofactor (dim_env env) n
        <|> Anomaly "evaluating unshifted term in too low-dimensional environment" in
      eval (Shift (env, mn, plusmap)) tm
  | Unact (op, tm) -> (
      match D.cofactor (dim_env env) (cod_op op) with
      | None ->
          fatal
            (Anomaly
               (Printf.sprintf
                  "evaluating unacted term in too low-dimensional environment: %s doesn't cofactor through %s"
                  (string_of_dim (dim_env env))
                  (string_of_dim (cod_op op))))
      | Some (Cofactor kn) ->
          let (Plus km) = D.plus (dom_op op) in
          let k = D.minus (dim_env env) kn in
          let op = plus_op k kn km op in
          eval (Act (env, opt_of_op op)) tm)
  | Shift (n, plusmap, tm) ->
      let (Plus mn) = D.plus n in
      eval (Unshift (env, mn, plusmap)) tm
  | Weaken tm -> eval (remove_top env) tm

and eval_with_boundary : type mode m a.
    (mode, m, a) env -> (mode, a, kinetic) term -> (m, (mode, kinetic) value) CubeOf.t =
 fun env tm ->
  CubeOf.build (dim_env env) { build = (fun fa -> eval_term (act_env env (opt_op_of_sface fa)) tm) }

(* Evaluate a cube of arguments for an application. *)
and eval_args : type mode m n mn a.
    (mode, m, a) env ->
    (m, n, mn) D.plus ->
    mn D.t ->
    (n, (mode, a, kinetic) term) CubeOf.t ->
    (mn, (mode, kinetic) value) CubeOf.t =
 fun env m_n mn tms ->
  CubeOf.build mn
    {
      build =
        (* Specifically, for each face of m+n... *)
        (fun fab ->
          (* ...we decompose it as a sum of a face "fa" of m and a face "fb" of n... *)
          let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
          (* ...and evaluate the supplied argument indexed by the face fb of n, in an environment acted on by the face fa of m. *)
          eval_term (act_env env (opt_op_of_sface fa)) (CubeOf.find tms fb));
    }

(* Apply a function value to an argument (with its boundaries). *)
and apply : type dom modality mode n m s.
    (mode, s) value ->
    (dom, modality, mode, n, m) Modality.filter_dim ->
    (n, (dom, kinetic) value) CubeOf.t ->
    (mode, s) evaluation =
 fun fn filter_nm arg ->
  let modality = Modality.filter_modality filter_nm in
  match view_term fn with
  (* If the function is a lambda-abstraction, we check that it has the correct dimension and mode and then beta-reduce, adding the arguments to the environment. *)
  | Lam (_, lam_filter, body) -> (
      let m = dim_binder body in
      let n = CubeOf.dim arg in
      match
        ( D.compare (Modality.filtered m lam_filter) n,
          Modality.compare (Modality.filter_modality lam_filter) modality )
      with
      | Eq, Eq -> apply_binder body lam_filter arg
      | Neq, _ -> fatal (Dimension_mismatch ("applying a lambda", m, n))
      | _, Neq ->
          fatal
            (Modality_mismatch
               (`Internal, "applying a lambda", Modality.filter_modality lam_filter, modality)))
  (* If it is a uninstantiated neutral application... *)
  | Neu { head; args; value; ty = (lazy ty) } -> (
      (* ... we check that its type is fully instantiated... *)
      match view_type ty "apply" with
      | Canonical (_, Pi { filter; doms; cods; _ }, ins, tyargs) -> (
          let pi_modality = Modality.filter_modality filter in
          (* ... and that the pi-type and its instantiation have the correct dimension. *)
          let k = CubeOf.dim doms in
          let m = BindCube.dim cods in
          let Eq = eq_of_ins_zero ins in
          match (D.compare (CubeOf.dim arg) k, Modality.compare pi_modality modality) with
          | Neq, _ -> fatal (Dimension_mismatch ("applying a neutral function", CubeOf.dim arg, k))
          | _, Neq ->
              fatal
                (Modality_mismatch (`Internal, "applying a neutral function", pi_modality, modality))
          | Eq, Eq -> (
              (* We annotate the new argument by its type, extracted from the domain type of the function being applied. *)
              let newarg = norm_of_vals_cube arg doms in
              (* We compute the output type of the application. *)
              let newty = lazy (tyof_app cods tyargs filter arg) in
              (* We add the new argument to the existing application spine. *)
              let args = Arg (args, filter, newarg, ins_zero m) in
              if GluedEval.read () then
                (* We add the argument to the lazy value and return a glued neutral. *)
                let value = apply_lazy value m filter newarg in
                Val (Neu { head; args; value; ty = newty })
              else
                (* We evaluate further with a case tree. *)
                match force_eval value with
                | Unrealized -> Val (Neu { head; args; value = ready Unrealized; ty = newty })
                (* It could be an indexed datatype waiting to be applied to more indices. *)
                | Val
                    (Canonical
                       {
                         mode;
                         canonical =
                           Data
                             {
                               dim;
                               tyfam;
                               indices = Unfilled _ as indices;
                               constrs;
                               discrete;
                               recursive;
                               hints;
                             };
                         tyargs = data_tyargs;
                         ins;
                         fields;
                         inst_fields = _;
                       }) -> (
                    let Eq = eq_of_ins_zero ins in
                    match
                      ( D.compare dim k,
                        D.compare_zero (TubeOf.inst data_tyargs),
                        (* Indices cannot have a nontrivial modal annotation *)
                        Modality.compare_id modality )
                    with
                    | Neq, _, _ -> fatal (Dimension_mismatch ("apply", dim, k))
                    | _, Pos _, _ ->
                        fatal
                          (Anomaly
                             "datatype was instantiated before being applied to all its indices")
                    | _, _, Neq ->
                        fatal
                          (Modality_mismatch
                             (`Internal, "apply", modality, Modality.id (Modality.tgt modality)))
                    | Eq, Zero, Eq ->
                        let indices = Fillvec.snoc indices newarg in
                        (* TODO: What happens to these?  What even are the fields of a not-fully-applied indexed datatype? *)
                        let fields =
                          match fields with
                          | Emp -> Bwd.Emp
                          | Snoc _ -> fatal (Unimplemented "fibrancy of indexed datatypes") in
                        let value =
                          Val
                            (Value.Canonical
                               {
                                 mode;
                                 canonical =
                                   Data { dim; tyfam; indices; constrs; discrete; recursive; hints };
                                 tyargs = TubeOf.empty dim;
                                 ins;
                                 fields;
                                 inst_fields = None;
                               }) in
                        Val (Neu { head; args; value = ready value; ty = newty }))
                | Val tm -> (
                    let value = apply tm filter_nm arg in
                    let newtm = Neu { head; args; value = ready value; ty = newty } in
                    match value with
                    | Realize x -> Val x
                    | Val (Canonical { canonical = Data d; _ }) ->
                        if Option.is_none !(d.tyfam) then
                          d.tyfam := Some (lazy { tm = newtm; ty = Lazy.force newty });
                        Val newtm
                    | _ -> Val newtm)
                | _ -> fatal (Anomaly "invalid application of type")))
      | _ -> fatal (Anomaly "invalid application by non-function"))
  | _ -> fatal (Anomaly "invalid application of non-function")

(* Compute the output type of a function application, given the codomains and instantiation arguments of the pi-type (the latter being the functions acting on the boundary) and the arguments it is applied to. *)
and tyof_app : type dom modality mode k n.
    (n, mode * modality * dom) BindCube.t ->
    (D.zero, n, n, mode normal) TubeOf.t ->
    (dom, modality, mode, k, n) Modality.filter_dim ->
    (k, (dom, kinetic) value) CubeOf.t ->
    (mode, kinetic) value =
 fun cods fns filter args ->
  let out_arg_tbl = Hashtbl.create 10 in
  let out_args =
    TubeOf.mmap
      {
        map =
          (fun fa [ { tm = afn; ty = _ } ] ->
            let fa = sface_of_tface fa in
            let (Filter_sface (fb, bf)) = Modality.filter_sface filter fa in
            let tmargs = CubeOf.subcube fb args in
            let (BindFam b) = BindCube.find cods fa in
            let tm = apply_term afn bf tmargs in
            let cod = apply_binder_term b bf tmargs in
            let ty =
              inst cod
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find out_arg_tbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let out_tm = { tm; ty } in
            Hashtbl.add out_arg_tbl (SFace_of fa) out_tm;
            out_tm);
      }
      [ fns ] in
  let (BindFam b) = BindCube.find_top cods in
  inst (apply_binder_term b filter args) out_args

(* Compute a field of a structure (or a fibrant type).  The modality is the left adjoint of the field's adjunction: the term being projected lives at its source mode (behind a lock by it), and the projection at its target mode.  For ordinary fields it is the identity. *)
and field : type src f mode n k nk s.
    (src, f, mode) Modality.t ->
    (src, s) value ->
    k Field.t ->
    (nk, n, k) insertion ->
    (mode, s) evaluation =
 fun fm tm fld fldins ->
  let src = Modality.src fm in
  match view_term tm with
  | Struct { fields; ins = structins; energy; eta = _ } -> (
      match (is_id_ins structins, D.compare (cod_left_ins structins) (dom_ins fldins)) with
      | Some _, Eq -> struct_field "struct" energy fm fields fld fldins
      | Some _, Neq ->
          fatal (Dimension_mismatch ("field of struct", cod_left_ins structins, dom_ins fldins))
      | None, _ -> fatal (Anomaly "nonidentity insertion when computing field of struct"))
  (* A canonical type can have fibrancy fields. *)
  | Canonical c -> (
      (* TODO: Do something with c.ins, in the case of glue. *)
      let fields = get_fibrancy_fields c in
      match D.compare (TubeOf.uninst c.tyargs) (dom_ins fldins) with
      | Neq ->
          fatal (Dimension_mismatch ("field of canonical", TubeOf.uninst c.tyargs, dom_ins fldins))
      | Eq -> struct_field "canonical" Potential fm fields fld fldins)
  | viewed_tm -> (
      (* We push the permutation from the insertion inside. *)
      let n, k = (cod_left_ins fldins, cod_right_ins fldins) in
      let (Plus fldplus) = D.plus k in
      let p = deg_of_perm (perm_inv (perm_of_ins_plus fldins fldplus)) in
      match act_value viewed_tm p (Modalcell.id2 src) with
      (* It must be an uninstantiated neutral application (which could be either an element of a record/codata, or a fibrant type). *)
      | Neu { head; args; value; ty = (lazy ty) } -> (
          let newty = lazy (tyof_field fm (Ok tm) ty fld ~shuf:Trivial fldins) in
          (* The stored filter is that of the field's modality at the (outer) result dimension n; the inner spine already lives at the corresponding filtered dimension.  For a fresh projection this filter is trivial; a nontrivial one arises only from a degeneracy having acted (see act_apps), which is exactly the situation when this is called from app_eval_apps to replay a filtered spine. *)
          let (Has_filter filter) = Modality.filter fm n in
          let args = Field (args, filter, fld, fldplus, ins_zero n) in
          if GluedEval.read () then
            let value = field_lazy fm value fld fldins in
            Val (Neu { head; args; value; ty = newty })
          else
            match force_eval value with
            | Unrealized -> Val (Neu { head; args; value = ready Unrealized; ty = newty })
            | Val tm -> (
                (* At this point we've already pushed the insertion inside in computing our neutral, so the remaining insertion on the field to compute of its value is "the identity" of appropriate dimensions *)
                let value = field fm tm fld (ins_of_plus n fldplus) in
                let newtm = Neu { head; args; value = ready value; ty = newty } in
                match value with
                | Realize x -> Val x
                | Val (Canonical { canonical = Data d; _ }) ->
                    if Option.is_none !(d.tyfam) then
                      d.tyfam := Some (lazy { tm = newtm; ty = Lazy.force newty });
                    Val newtm
                | _ -> Val newtm)
            | Realize _ -> fatal (Anomaly "realized neutral"))
      | _ ->
          fatal ~severity:Asai.Diagnostic.Bug
            (No_such_field (`Other (Dump.Val tm), `Ins (fld, fldins))))

and struct_field : type src f mode s et n k nk.
    ?unset_ok:bool ->
    string ->
    s energy ->
    (src, f, mode) Modality.t ->
    (src * nk * s * et) StructfieldAbwd.t ->
    k Field.t ->
    (nk, n, k) insertion ->
    (mode, s) evaluation =
 fun ?(unset_ok = false) err energy fm fields fld fldins ->
  match StructfieldAbwd.find_opt fields fld with
  | Found (Lower (adj, v, _)) -> (
      (* The projecting modality must be the left adjoint of the field's stored adjunction, since typechecking ensured it. *)
      match Modality.compare (Modalcell.adj_left adj) fm with
      | Neq -> fatal (Anomaly ("modality mismatch in projecting " ^ err ^ " field"))
      | Eq ->
          (* The value supplied by the tuple/comatch is keyed by the adjunction counit, taking it from behind the composite lock (right adjoint inside, then left adjoint) to the ambient context.  For ordinary fields the counit is the identity and this is a no-op. *)
          let (Adjunction { counit; _ }) = adj in
          act_evaluation (force_eval v) (id_deg D.zero) counit)
  | Found (Higher (lazy { adj; vals; intrinsic; _ })) -> (
      (* Like a lower field, the projecting modality must be the left adjoint of the field's stored adjunction. *)
      match Modality.compare (Modalcell.adj_left adj) fm with
      | Neq -> fatal (Anomaly ("modal projection of higher " ^ err ^ " field"))
      | Eq -> (
          match D.compare intrinsic (cod_right_ins fldins) with
          | Eq -> (
              match InsmapOf.find fldins vals with
              (* As for lower fields, the stored value lives behind the composite lock and is keyed by the counit to bring it to the ambient context.  For ordinary fields the counit is the identity and this is a no-op. *)
              | Some v ->
                  let (Adjunction { counit; _ }) = adj in
                  act_evaluation (force_eval v) (id_deg D.zero) counit
              | None ->
                  if unset_ok then Unrealized else fatal (Anomaly (err ^ " field value unset")))
          | Neq ->
              fatal (Dimension_mismatch (err ^ " field intrinsic", intrinsic, cod_right_ins fldins))
          ))
  | _ -> (
      match energy with
      | Potential -> Unrealized
      | Kinetic -> fatal (Anomaly ("missing field in eval struct: " ^ Field.to_string fld)))

and field_term : type src f mode n k nk.
    (src, f, mode) Modality.t ->
    (src, kinetic) value ->
    k Field.t ->
    (nk, n, k) insertion ->
    (mode, kinetic) value =
 fun fm x fld fldins ->
  let (Val v) = field fm x fld fldins in
  v

(* Given a term and its record type, compute the type of a field projection, and the substitution dimension it was evaluated at.  There are two versions of this function, one for when we already know the insertion associated to the field, and one for when we are synthesizing it from the user's integer sequence.  First we define the shared part of both, where we have already found the codatafield from the codata type.  We allow the term to be an error, in case typechecking failed earlier but we are continuing on; this can nevertheless succeed (or fail in more interesting ways) if the type doesn't actually depend on that value. *)

and tyof_codatafield : type src f mode m n mn a k r s i et.
    (src, f, mode) Modality.t ->
    ((src, kinetic) value, Code.t) Result.t ->
    i Field.t ->
    (i, src * a * n * et) Codatafield.t ->
    (src, m, a) env ->
    (D.zero, mn, mn, src normal) TubeOf.t ->
    m D.t ->
    (m, n, mn) D.plus ->
    (* We allow passing through a shuffle and eval-readback as well, in the case that this is a higher field being called recursively as part of the instantiation arguments. *)
    shuf:(src, r, k, i, a) shuffleable ->
    (m, s, k) insertion ->
    (mode, kinetic) value =
 fun fm tm fldname fldty env tyargs m mn ~shuf fldins ->
  (* The type of the field projection comes from the type associated to that field name in general, evaluated at the stored environment extended by the term itself and its boundaries. *)
  match fldty with
  | Term.Codatafield.Lower (adj, plus_lock, fldty) -> (
      (* The projecting modality must be the left adjoint of the field's adjunction; the caller is responsible for having checked this with a user-facing error when synthesizing. *)
      match Modality.compare (Modalcell.adj_left adj) fm with
      | Neq -> fatal (Anomaly "wrong locking modality in tyof_codatafield")
      | Eq -> tyof_lower_codatafield tm fldname adj plus_lock fldty env tyargs m mn ~key:`Counit)
  | Term.Codatafield.Higher (adj, ic0, plus_lock, fldty) -> (
      (* Like a lower field, the projecting modality must be the left adjoint of the field's adjunction. *)
      match Modality.compare (Modalcell.adj_left adj) fm with
      | Neq -> fatal (Anomaly "wrong locking modality of higher field in tyof_codatafield")
      | Eq ->
          let Eq = D.plus_uniq mn (D.plus_zero m) in
          tyof_higher_codatafield tm fldname adj env tyargs fldins ic0 plus_lock fldty ~shuf
            ~key:`Counit)

(* We dispatch to separate helper functions for lower fields and higher fields that assume all the dimensions are correct.  These helper functions can be called directly by a caller who knows that all the dimensions are correct, such as check_field where the field is obtained by iterating directly through the codatatype.

   The ~key flag distinguishes two uses.  `Counit computes the type of a *projection* x .fld, which is keyed by the adjunction counit to put it in the ambient context (rule 3 of modal fields).  `Nokey computes the type at which the *component* of a tuple/comatch is checked or read back, which lives behind the lock by the right adjoint and is not keyed (rule 2).  For ordinary fields the two agree, since the counit is the identity. *)
and tyof_lower_codatafield : type amode m n mn a f g gmode ag.
    ((amode, kinetic) value, Code.t) Result.t ->
    D.zero Field.t ->
    (amode, f, g, gmode) Modalcell.adjunction ->
    ((a, (amode id, n) dim_entry) snoc, amode, g, gmode, ag) plus_lock ->
    (gmode, ag, kinetic) term ->
    (amode, m, a) env ->
    (D.zero, mn, mn, amode normal) TubeOf.t ->
    m D.t ->
    (m, n, mn) D.plus ->
    key:[ `Counit | `Nokey ] ->
    (gmode, kinetic) value =
 fun tm fldname adj plus_lock fldty env tyargs m mn ~key ->
  let values =
    match tm with
    | Ok tm -> `Ok (TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm))
    | Error e -> `Error e in
  let amode = mode_env env in
  let (Adjunction { left; counit; _ }) = adj in
  let env =
    Value.Ext
      {
        env;
        plus = mn;
        filter = Modality.filter_id amode m;
        filtered = Modality.filter_id amode (D.plus_right mn);
        values;
      } in
  (* The type of a modal field lives behind a lock by the right adjoint, so we key the environment by its identity cell. *)
  let env = key_id_env env plus_lock in
  (* This type is m-dimensional, hence must be instantiated at a full m-tube. *)
  let insttm = eval_term env fldty in
  (* The type of a field projection is keyed by the adjunction counit, to put it in the ambient context (where the term being projected lives behind a lock by the left adjoint).  For ordinary fields the counit is the identity and this is a no-op. *)
  let insttm =
    match key with
    | `Counit -> act_value insttm (id_deg D.zero) counit
    | `Nokey -> insttm in
  let instargs =
    TubeOf.mmap
      {
        map =
          (fun fa [ arg ] ->
            let fains = ins_zero (dom_tface fa) in
            let tm = field_term left arg.tm fldname fains in
            let ty = tyof_field left (Ok arg.tm) arg.ty fldname ~shuf:Trivial fains in
            { tm; ty });
      }
      [ fst (TubeOf.split (D.zero_plus m) mn tyargs) ] in
  inst insttm instargs

(* Compute the non-keyed component type of a lower field of a record type value, along with the field's adjunction: the type at which the stored component of a tuple lives, behind the lock by the right adjoint.  Used when reading back a struct at a record type. *)
and tyof_field_nokey : type amode.
    ((amode, kinetic) value, Code.t) Result.t ->
    (amode, kinetic) value ->
    D.zero Field.t ->
    amode tyof_modal_field =
 fun tm ty fld ->
  match view_type ty "tyof_field_nokey" with
  | Canonical (_, Codata { env; fields; _ }, codatains, tyargs) -> (
      match is_id_ins codatains with
      | None -> fatal (Anomaly "degenerated record in tyof_field_nokey")
      | Some mn -> (
          let m = dim_env env in
          match Term.CodatafieldAbwd.find_opt fields fld with
          | Found (Lower (adj, plus_lock, fldty)) ->
              Tyof_modal_field
                (adj, tyof_lower_codatafield tm fld adj plus_lock fldty env tyargs m mn ~key:`Nokey)
          | _ -> fatal (Anomaly "field not found in tyof_field_nokey")))
  | _ -> fatal (Anomaly "non-codatatype in tyof_field_nokey")

(* This function is also called directly from check_higher_field.  In that case, the field is determined by a partial bijection that may *not* be just an insertion, and we have to frobnicate the environment in which we evaluate the type.  Some of that frobnication involves an eval-readback cycle, which requires a callback from here since readback isn't defined yet. *)
and tyof_higher_codatafield : type mode f g gmode c n h s r i ic iag.
    ((mode, kinetic) value, Code.t) Result.t ->
    i Field.t ->
    (* A higher field is modal over an adjunction, just like a lower field.  Its type is checked (and hence lives) behind a lock by the right adjoint, at the right adjoint's source mode; ordinary fields use the identity adjunction.  We currently require the modality to be fully parametric, so it filters no dimensions of the field. *)
    (mode, f, g, gmode) Modalcell.adjunction ->
    (* The codatatype is in context of length c.  It has been evaluated at dimension n, in an (n, c) env. *)
    (mode, n, c) env ->
    (* And so it has a boundary n-tube. *)
    (D.zero, n, n, mode normal) TubeOf.t ->
    (* The field has intrinsic dimension i, determined by a pbij from n to i, with result s, remaining r, shared h.  We record the insertion and shuffle separately, with a shuffleable recording explicitly whether the shuffle is nontrivial and including a readback callback if so.  This is because we will have to readback a (s+h, [c;0]) env, in some context, and evaluate in an (r,a) env coming from degenerating that context, to get an (r+s+h, [c;0]) env, but readback depends on this file. *)
    (n, s, h) insertion ->
    (* It's very important that these callbacks be called on *all values* before they are used, including tm, env, and tyargs, since they start out in the non-degenerated context but everything has to actually happen in the degenerated one. *)
    shuf:(mode, r, h, i, c) shuffleable ->
    (* We add i to all the dimensions in [c;0] to get i+[c;0]. *)
    (i, (c, (mode id, D.zero) dim_entry) snoc, ic, mode) plusmap ->
    (* Then we lock by the right adjoint g to get the context iag at its source mode gmode. *)
    (ic, mode, g, gmode, iag) plus_lock ->
    (* The unevaluated type of the field is a term in context of this length i+[c;0], locked by g.  The extra 0 is for the 'self' variable, which is always 0-dimensional when *defining* the codatatype. *)
    (gmode, iag, kinetic) term ->
    (* As for lower fields, ~key:`Counit keys the result by the adjunction counit (for a projection) while ~key:`Nokey leaves it behind the g-lock (for checking/reading back a tuple component). *)
    key:[ `Counit | `Nokey ] ->
    (* In the nontrivial case, the return value is also in the degenerated context. *)
    (gmode, kinetic) value =
 fun tm fldname adj codataenv tyargs fldins ~shuf ic0 plus_lock fldty ~key ->
  let n = dom_ins fldins in
  let s = cod_left_ins fldins in
  let h =
    cod_right_ins fldins
    (* = right_shuffle fldshuf *) in
  let (Plus rh) = D.plus h in
  let (Plus rs) = D.plus s in
  let (Plus sh) = D.plus h in
  let (Plus r_sh) = D.plus (D.plus_out s sh) in
  let rs_h = D.plus_assocl rs sh r_sh in
  (* We extend the (n, c) env by a variable for the current term, getting an (n, [c;0]) env.  *)
  let values =
    match tm with
    | Ok tm -> `Ok (TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm))
    | Error e -> `Error e in
  let mode = mode_env codataenv in
  let (Adjunction { left; counit; _ }) = adj in
  let env =
    Value.Ext
      {
        env = codataenv;
        plus = D.plus_zero n;
        filter = Modality.filter_id mode n;
        filtered = Modality.filter_zero (Modality.id mode);
        values;
      } in
  (* Now we act on this (n, [c;0]) env by the inverse of the insertion to get an (s+h, [c;0]) env. *)
  let env = Act (env, opt_op_of_deg (deg_of_perm (perm_inv (perm_of_ins_plus fldins sh)))) in
  let env =
    match shuf with
    (* When r=0 and h=i, we can just shift this to get an (s, h+[c;0]) env, which is the same as (s, i+[c;0]), so it matches the context of fldty. *)
    | Trivial -> Shift (env, sh, ic0)
    (* In the general case... *)
    | Nontrivial { dbwd = _; shuffle; deg_env; deg_nf = _ } ->
        (* First we do some dimension arithemetic. *)
        let r = left_shuffle shuffle in
        let i = out_shuffle shuffle in
        let (Plus si) = D.plus i in
        let (Plus sr) = D.plus r in
        let (Plus sr_h) = D.plus h in
        let s_rh = D.plus_assocr sr rh sr_h in
        (* Then we eval-readback to get an (r+s+h, [c;0]) env. *)
        let env = deg_env sh r_sh env in
        (* Then we permute it to get an (s+r+h, [c;0]) env, and act by the shuffle to get (s+i, [c;0]) *)
        let swapdeg = deg_plus (swap_deg sr rs) rs_h sr_h in
        let shuffledeg = plus_deg s s_rh si (deg_of_shuffle shuffle rh) in
        let env = Value.Act (env, opt_op_of_deg (comp_deg swapdeg shuffledeg)) in
        (* Finally, now we can shift this to get a (s, i+[c;0]) env. *)
        Shift (env, si, ic0) in
  (* The field type lives behind a lock by the right adjoint, so we key the environment by it (by identity cells, per generator) before evaluating. *)
  let env = key_id_env env plus_lock in
  (* Now this matches the context of fldty, so we can evaluate it. *)
  let insttm = eval_term env fldty in
  (* The type of a field projection is keyed by the adjunction counit, to put it in the ambient context (where the term being projected lives behind a lock by the left adjoint).  For ordinary fields the counit is the identity and this is a no-op. *)
  let insttm =
    match key with
    | `Counit -> act_value insttm (id_deg D.zero) counit
    | `Nokey -> insttm in
  (* Since the result is s-dimensional, it has to be instantiated at a full s-tube. *)
  let instargs =
    TubeOf.build D.zero (D.zero_plus s)
      {
        build =
          (fun (type k) (fa : (k, s) pface) ->
            (* To get the instantiation arguments, we have to lift the faces along the field insertion to get the new insertion and the face to access.  *)
            let (Pface_lift_ins (type m) ((fains, faplus) : (m, k, h) insertion * (m, n) pface)) =
              pface_lift_ins fa fldins in
            let arg = TubeOf.find tyargs faplus in
            match shuf with
            | Trivial ->
                let tm = field_term left arg.tm fldname fains in
                let ty = tyof_field left (Ok arg.tm) arg.ty fldname ~shuf fains in
                { tm; ty }
            | Nontrivial { dbwd = _; shuffle; deg_env = _; deg_nf } ->
                (* In this case, we have to degenerate the arguments, since they depend on the context. *)
                let arg = deg_nf arg in
                (* We also use these extra dimensions to make the pbij into an insertion. *)
                let (Plus rm) = D.plus (dom_tface faplus) in
                let arg_ins = ins_plus_of_pbij fains shuffle rm in
                let tm = field_term left arg.tm fldname arg_ins in
                let ty = tyof_field left (Ok arg.tm) arg.ty fldname ~shuf:Trivial arg_ins in
                { tm; ty });
      } in
  inst insttm instargs

(* This version is when we already know the insertion.  In this case, it's a bug if the field name or dimension don't match.  The modality is the left adjoint of the field's adjunction: the term and its type live at its source mode and the resulting field type at its target mode. *)
and tyof_field : type src f mode m h s r i c.
    (src, f, mode) Modality.t ->
    ((src, kinetic) value, Code.t) Result.t ->
    (src, kinetic) value ->
    i Field.t ->
    (* We allow passing through a shuffle and eval-readback as well, in the case that this is a higher field being called recursively as part of the instantiation arguments. *)
    shuf:(src, r, h, i, c) shuffleable ->
    (m, s, h) insertion ->
    (mode, kinetic) value =
 fun fm tm ty fld ~shuf fldins ->
  let errtm =
    match tm with
    | Ok tm -> Dump.Val tm
    | Error _err -> PString "[ERROR]" in
  let errfld =
    match shuf with
    | Trivial -> `Ins (fld, fldins)
    | Nontrivial { shuffle; _ } -> `Pbij (fld, Pbij (fldins, shuffle)) in
  let severity = Asai.Diagnostic.Bug in
  match view_type ty "tyof_field" with
  | Canonical
      (type hmode mn m n)
      (( head,
         Codata
           (type d a et)
           ({ env; fields; opacity = _; eta; termctx = _; hints = _ } :
             (src, m, n, d, a, et) codata_args),
         codatains,
         tyargs ) :
        hmode head
        * (src, m, n) canonical
        * (mn, m, n) insertion
        * (D.zero, mn, mn, src normal) TubeOf.t) -> (
      (* The type cannot have a nonidentity degeneracy applied to it (though it can be at a higher dimension). *)
      match is_id_ins codatains with
      | None -> fatal ~severity (No_such_field (`Degenerated_record eta, errfld))
      | Some mn -> tyof_field_giventype fm tm head eta env mn fields tyargs fld ~shuf fldins)
  | Canonical (head, UU (srcmode, m), ins, tyargs) -> (
      let Eq = eq_of_ins_zero ins in
      let err = Code.No_such_field (`Type errtm, errfld) in
      match Fibrancy.FieldsMap.find_opt srcmode !Fibrancy.fields with
      | None -> fatal ~severity err
      | Some fields ->
          let values =
            match tm with
            | Ok tm -> `Ok (TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm))
            | Error e -> `Error e in
          let env =
            Value.Ext
              {
                env = Value.Emp (srcmode, m);
                plus = D.plus_zero m;
                filter = Modality.filter_id srcmode m;
                filtered = Modality.filter_zero (Modality.id srcmode);
                values;
              } in
          tyof_field_giventype fm tm head Noeta env (D.plus_zero m) fields tyargs fld ~shuf fldins)
  | _ ->
      let p =
        match tm with
        | Ok tm -> Dump.Val tm
        | Error _err -> PString "[ERROR]" in
      fatal ~severity (No_such_field (`Other p, errfld))

and tyof_field_giventype : type src f mode m n mn h s r i c et a k hmode.
    (src, f, mode) Modality.t ->
    ((src, kinetic) value, Code.t) Result.t ->
    hmode head ->
    (potential, et) eta ->
    (src, m, a) env ->
    (m, n, mn) D.plus ->
    (src * a * n * et) Term.CodatafieldAbwd.t ->
    (D.zero, mn, mn, src normal) TubeOf.t ->
    i Field.t ->
    shuf:(src, r, h, i, c) shuffleable ->
    (k, s, h) insertion ->
    (mode, kinetic) value =
 fun fm tm head eta env mn fields tyargs fld ~shuf fldins ->
  let severity = Asai.Diagnostic.Bug in
  let errfld =
    match shuf with
    | Trivial -> `Ins (fld, fldins)
    | Nontrivial { shuffle; _ } -> `Pbij (fld, Pbij (fldins, shuffle)) in
  let m = dim_env env in
  (* Note that n is the Gel dimension while m is the evaluation dimension.  So we need an m+n tube of type arguments, but the insertion labeling the field being accessed has only m as its evaluation dimension. *)
  match D.compare m (dom_ins fldins) with
  | Neq ->
      fatal ~severity
        (Dimension_mismatch ("tyof_field evaluation " ^ Field.to_string fld, m, dom_ins fldins))
  | Eq -> (
      match Term.CodatafieldAbwd.find_opt fields fld with
      | Found fldty ->
          let shuf : (src, r, h, i, a) shuffleable =
            match shuf with
            | Trivial -> Trivial
            | Nontrivial { dbwd; _ } -> (
                match Tctx.compare dbwd (length_env env) with
                | Eq -> shuf
                | Neq -> fatal (Anomaly "context length mismatch in tyof_field")) in
          tyof_codatafield fm tm fld fldty env tyargs m mn ~shuf fldins
      | Not_found -> fatal ~severity (No_such_field (`Record (eta, phead head), errfld))
      | Wrong_dimension (i, _) ->
          let errsuffix =
            match shuf with
            | Trivial -> `Ins fldins
            | Nontrivial { shuffle; _ } -> `Pbij (Pbij (fldins, shuffle)) in
          fatal ~severity (Wrong_dimension_of_field (eta, phead head, `Field fld, m, i, errsuffix)))

(* This version is for when we are synthesizing the insertion, so we return the resulting insertion along with the type.  The field might also be given positionally in this case, so we also return the field name when we find it.  In this case, mismatches in field names or dimensions are user errors, as is a mismatch between the locking modality (from the user's annotation, or the identity if none) and the left adjoint of the field's adjunction. *)
and tyof_field_withname : type src f mode a b.
    (src, f, mode) Modality.t ->
    (src, a, b) Ctx.t ->
    ((src, kinetic) value, Code.t) Result.t ->
    (src, kinetic) value ->
    [ `Name of string * int list | `Int of int ] ->
    Field.with_ins * (mode, kinetic) value =
 fun fm ctx tm ty infld ->
  let errfld =
    match infld with
    | `Name (str, ints) -> `Strings (str, ints)
    | `Int n -> `Int n in
  let errtm =
    match tm with
    | Ok tm -> PVal (ctx, tm)
    | Error _err -> PString "[ERROR]" in
  match view_type ~severity:Asai.Diagnostic.Error ty "tyof_field" with
  | Canonical
      (head, Codata { env; fields; opacity = _; eta; termctx = _; hints = _ }, codatains, tyargs)
    -> (
      (* The type cannot have a nonidentity degeneracy applied to it (though it can be at a higher dimension). *)
      match is_id_ins codatains with
      | None -> fatal (No_such_field (`Degenerated_record eta, errfld))
      | Some mn ->
          let err = Code.No_such_field (`Record (eta, phead head), errfld) in
          tyof_field_withname_giventype fm ctx tm ty eta env mn fields tyargs infld err)
  | Canonical (_head, UU (srcmode, m), ins, tyargs) -> (
      let Eq = eq_of_ins_zero ins in
      let err = Code.No_such_field (`Type errtm, errfld) in
      match Fibrancy.FieldsMap.find_opt srcmode !Fibrancy.fields with
      | None -> fatal err
      | Some fields ->
          let values =
            match tm with
            | Ok tm -> `Ok (TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm))
            | Error e -> `Error e in
          let env =
            Value.Ext
              {
                env = Value.Emp (srcmode, m);
                plus = D.plus_zero m;
                filter = Modality.filter_id srcmode m;
                filtered = Modality.filter_zero (Modality.id srcmode);
                values;
              } in
          tyof_field_withname_giventype fm ctx tm ty Noeta env (D.plus_zero m) fields tyargs infld
            err)
  | _ -> fatal (No_such_field (`Other errtm, errfld))

(* Subroutine of tyof_field_withname for after we've identified the type of the head as either a codatatype or a universe (for fibrancy fields). *)
and tyof_field_withname_giventype : type src f mode a b m n mn c et.
    (src, f, mode) Modality.t ->
    (src, a, b) Ctx.t ->
    ((src, kinetic) value, Code.t) Result.t ->
    (src, kinetic) value ->
    (potential, et) eta ->
    (src, m, c) env ->
    (m, n, mn) D.plus ->
    (src * c * n * et) Term.CodatafieldAbwd.t ->
    (D.zero, mn, mn, src normal) TubeOf.t ->
    [ `Name of string * int list | `Int of int ] ->
    Code.t ->
    Field.with_ins * (mode, kinetic) value =
 fun fm ctx tm ty eta env mn fields tyargs infld err ->
  let m = dim_env env in
  (* Check that the locking modality supplied by the user (or the identity, if none) agrees with the left adjoint of the adjunction stored with the field, and that the field is present (not filtered away by a nonparametric modality) at the current dimension. *)
  let check_modality : type i. i Field.t -> (i, src * c * n * et) Term.Codatafield.t -> unit =
   fun fld fldty ->
    let mismatch : type d1 m1 c1. (d1, m1, c1) Modality.t -> unit =
     fun left ->
      let field = Field.to_string fld in
      match (Modality.compare_id left, Modality.compare_id fm) with
      | Eq, Eq -> fatal (Anomaly "unequal identity modalities")
      | Eq, Neq -> fatal (Wrong_locking_modality { field; expected = None; got = Some fm })
      | Neq, Eq -> fatal (Wrong_locking_modality { field; expected = Some left; got = None })
      | Neq, Neq -> fatal (Wrong_locking_modality { field; expected = Some left; got = Some fm })
    in
    match fldty with
    | Lower (adj, _, _) -> (
        let left = Modalcell.adj_left adj in
        match Modality.compare left fm with
        | Neq -> mismatch left
        | Eq -> (
            (* The field disappears if its nonparametric modality filters this dimension nontrivially. *)
            let (Has_filter left_filter) = Modality.filter left m in
            match Modality.filter_is_trivial m left_filter with
            | Some Eq -> ()
            | None -> fatal (Modal_field_filtered_away (Field.to_string fld, left))))
    | Higher (adj, _, _, _) -> (
        (* Like a lower field, a higher field's projecting modality must be the left adjoint. *)
        let left = Modalcell.adj_left adj in
        match Modality.compare left fm with
        | Neq -> mismatch left
        | Eq -> (
            (* The field disappears if its nonparametric modality filters this dimension nontrivially.  (Currently unreachable, since we require modal higher fields to be parametric at definition time; but this keeps the check robust.) *)
            let (Has_filter left_filter) = Modality.filter left m in
            match Modality.filter_is_trivial m left_filter with
            | Some Eq -> ()
            | None -> fatal (Modal_field_filtered_away (Field.to_string fld, left)))) in
  let m = dim_env env in
  match infld with
  | `Name (fldname, ints) -> (
      match ins_of_ints m ints with
      | None -> fatal (Invalid_field_suffix (PVal (ctx, ty), fldname, ints, m))
      | Some (Ins_of fldins) -> (
          let i = cod_right_ins fldins in
          let fld = Field.intern fldname i in
          match Term.CodatafieldAbwd.find_opt fields fld with
          | Found fldty ->
              check_modality fld fldty;
              let fldty = tyof_codatafield fm tm fld fldty env tyargs m mn ~shuf:Trivial fldins in
              (WithIns (fld, fldins), fldty)
          | Wrong_dimension (i, fldty) -> (
              (* If the user omitted the suffix completely, and the field and the term are both 1-dimensional, we fill in the unique suffix "1" for them. *)
              let err =
                Code.Wrong_dimension_of_field
                  (eta, PVal (ctx, ty), `String fldname, m, i, `Ints ints) in
              match (ints, D.compare m i, D.compare_zero m) with
              | [], Eq, Pos m' -> (
                  let (Is_suc (mpred, _, _)) = suc_pos m' in
                  match D.compare_zero mpred with
                  | Zero ->
                      let fld = Field.intern fldname i in
                      let fldins = zero_ins m in
                      check_modality fld fldty;
                      let fldty =
                        tyof_codatafield fm tm fld fldty env tyargs m mn ~shuf:Trivial fldins in
                      (WithIns (fld, fldins), fldty)
                  | Pos _ -> fatal err)
              | _ -> fatal err)
          | Not_found -> fatal err))
  | `Int k -> (
      try
        let (Entry (fld, fldty)) = List.nth (Bwd.to_list fields) k in
        match D.compare_zero (Field.dim fld) with
        | Zero ->
            let fldins = ins_zero m in
            check_modality fld fldty;
            let fldty = tyof_codatafield fm tm fld fldty env tyargs m mn ~shuf:Trivial fldins in
            (WithIns (fld, fldins), fldty)
        | Pos _ -> fatal err
      with Failure _ -> fatal err)

and apply_binder : type dom modality mode kl mn s.
    (mode, modality, dom, mn, s) Value.binder ->
    (dom, modality, mode, kl, mn) Modality.filter_dim ->
    (kl, (dom, kinetic) value) CubeOf.t ->
    (mode, s) evaluation =
 fun (Value.Bind { env; modality; filter = filter_l_n; ins; body }) filter_kl_mn argstbl ->
  let m = dim_env env in
  let n = cod_right_ins ins in
  let l = Modality.filtered n filter_l_n in
  let (Plus mn) = D.plus n in
  let perm = perm_of_ins_plus ins mn in
  let (Has_filter filter_k_m) = Modality.filter modality m in
  let k = Modality.filtered m filter_k_m in
  let (Plus kl) = D.plus l in
  let (Filter_perm (filtered_perm, filter_kl_mn')) =
    Modality.filter_perm (Modality.filter_plus kl mn filter_k_m filter_l_n) perm in
  let Eq = Modality.filter_uniq filter_kl_mn filter_kl_mn' in
  let filtered_perm_inv = perm_inv filtered_perm in
  (* The arguments have to be acted on by degeneracies to form the appropriate cube.  But not all the arguments may be actually used, so we do these actions lazily. *)
  act_evaluation
    (eval
       (Ext
          {
            env;
            plus = kl;
            filter = filter_k_m;
            filtered = Modality.filter_idempotent filter_l_n;
            values =
              `Lazy
                (CubeOf.build (D.plus_out k kl)
                   {
                     build =
                       (fun frfs ->
                         let (Face (fa, fb)) = perm_sface filtered_perm_inv frfs in
                         act_lazy_eval
                           (defer (Modality.src modality) (fun () -> Val (CubeOf.find argstbl fa)))
                           (deg_of_perm fb)
                           (Modalcell.id2 (Modality.src modality)));
                   });
          })
       body)
    (deg_of_perm perm)
    (Modalcell.id2 (mode_env env))

and eval_canonical : type mode m a.
    (mode, m, a) env -> (mode, a) Term.canonical -> (mode, potential) evaluation =
 fun env can ->
  match can with
  | Data { indices; constrs; discrete; recursive; hints } ->
      let tyfam = ref None in
      let constrs =
        Abwd.map
          (fun (Term.Dataconstr { args; indices }) -> Value.Dataconstr { env; args; indices })
          constrs in
      let dim, mode = (dim_env env, mode_env env) in
      let canonical =
        Data { dim; tyfam; indices = Fillvec.empty indices; constrs; discrete; recursive; hints }
      in
      let tyargs = TubeOf.empty (dim_env env) in
      let fields =
        match Lazy.force Fibrancy.data with
        | None -> Bwd.Emp
        | Some () -> fatal (Unimplemented "fibrancy of datatypes") in
      Val
        (Canonical
           { mode; canonical; tyargs; ins = ins_zero dim; fields; inst_fields = Some fields })
  | Codata c ->
      eval_codata env c.eta c.opacity c.hints c.dim (Lazy.from_val c.termctx) c.fields
        (Fibrancy.Codata.finished (mode_env env) c)

(* We split out this subroutine so it can be called from Check.with_codata_so_far and a lazy termctx.  *)
and eval_codata : type mode m a c n et.
    (mode, m, a) env ->
    (potential, et) eta ->
    opacity ->
    hints ->
    n D.t ->
    (mode, c, (a, (mode id, n) dim_entry) snoc) termctx option Lazy.t ->
    (mode * a * n * et) CodatafieldAbwd.t ->
    (mode * (n * a * potential * no_eta)) Term.StructfieldAbwd.t ->
    (mode, potential) evaluation =
 fun env eta opacity hints n termctx fields fibrancy_fields ->
  let m = dim_env env in
  let (Plus (type mn) (m_n : (m, n, mn) D.plus)) = D.plus n in
  let mn = D.plus_out m m_n in
  let ins = id_ins m m_n in
  let canonical = Codata { eta; opacity; hints; env; termctx; fields } in
  let tyargs = TubeOf.empty mn in
  let fields = eval_structfield_abwd env m m_n mn fibrancy_fields in
  Val (Canonical { mode = mode_env env; canonical; tyargs; ins; fields; inst_fields = Some fields })

and eval_term : type mode m b. (mode, m, b) env -> (mode, b, kinetic) term -> (mode, kinetic) value
    =
 fun env tm ->
  let (Val v) = eval env tm in
  v

and eval_env : type mode a q n qn b.
    (mode, q, a) env -> (q, n, qn) D.plus -> (mode, a, n, b) Term.env -> (mode, qn, b) Value.env =
 fun env q_n tmenv ->
  let q = dim_env env in
  let qn = D.plus_out q q_n in
  let n = D.plus_right q_n in
  match tmenv with
  | Emp (mode, _) -> Emp (mode, qn)
  (* another dimension here *)
  | Ext
      {
        env = tmenv;
        plus = m_k;
        values = Modal (modality, al, xss);
        filtered = filt_k_k;
        filter = filt_m_n;
      } ->
      let evalled_env : (mode, qn, _) Value.env = eval_env env q_n tmenv in
      let k = D.plus_right m_k in
      let (Has_filter filt_p_q) = Modality.filter modality q in
      let p = Modality.filtered q filt_p_q in
      let m = Modality.filtered n filt_m_n in
      let (Plus p_m) = D.plus m in
      let filt_pm_qn = Modality.filter_plus p_m q_n filt_p_q filt_m_n in
      let (Plus pm_k) = D.plus k in
      let p_mk = D.plus_assocr p_m m_k pm_k in
      let pmk = D.plus_out p p_mk in
      let lenv = key_id_env env al in
      let flenv = act_env lenv (opt_op_of_opt_sface (Modality.sface_of_filter q filt_p_q)) in
      (* We make everything lazy, since we can, and not everything may end up being used. *)
      Value.Ext
        {
          env = evalled_env;
          plus = pm_k;
          filter = filt_pm_qn;
          filtered = filt_k_k;
          values =
            `Lazy
              (CubeOf.build pmk
                 {
                   build =
                     (fun fab ->
                       let (SFace_of_plus (_, fa, fb)) = sface_of_plus p_mk fab in
                       lazy_eval (act_env flenv (opt_op_of_sface fa)) (CubeOf.find xss fb));
                 });
        }
  | Key { env = tmenv; cell; plus_src; plus_tgt } -> (
      let (Restrict_keys (env, extra, mu12, keys, pre)) = restrict_keys env plus_tgt in
      match extra with
      | Plus_lock (Zero _, Zero) ->
          let Eq = Modality.comp_uniq mu12 (Modality.id_comp (Modalcell.vtgt cell)) in
          prekey_env (Key (eval_env env q_n tmenv, Modalcell.vcomp keys cell, plus_src)) pre
      | Plus_lock (Suc _, _) ->
          (* The split landed in the middle of a key, so restrict_keys slurped the rest of that key's locks (extra) and folded its whole cell into keys, which therefore lives at a deeper mode than cell and can't be vertically composed with it.  Unlike a term Key, we can't extend plus_src by the extra either, since it lies on the codomain base of the term environment while the extra lies on its domain base.  So we rebuild the extra locks as identity keys to realign the residual environment with the term environment's domain, and apply the composite keys as a prekey action outside the resulting Key, where the accumulated actions compose in the same order as before. *)
          prekey_env
            (prekey_env (Key (eval_env (key_id_env env extra) q_n tmenv, cell, plus_src)) keys)
            pre)
  (* A term prekey is evaluated just like a key, except that the composite cell mediates the value environment on the domain side, before evaluating the inner term environment, rather than being wrapped around the result on the codomain side. *)
  | Prekey { env = tmenv; cell; plus_src; plus_tgt } ->
      let (Restrict_keys (env, extra, mu12, keys, pre)) = restrict_keys env plus_tgt in
      (* As in the Key branch of eval, if restrict_keys had to slurp up extra locks from the middle of a key, we postwhisker the cell by their composite modality so that its target matches the source of the composite keys, and extend the source locks of the resulting key by the extra.  (Here, unlike in the Key branch of eval_env, plus_src lies on the same base as plus_tgt, so this is possible.) *)
      let (Comp nu12) = Modality.comp (Modalcell.vsrc cell) in
      let extra_cell = Modalcell.postwhisker nu12 mu12 (plus_lock_modality extra) cell in
      let kenv =
        key_env env (Modalcell.vcomp keys extra_cell) (plus_lock_comp extra plus_src nu12) in
      prekey_env (eval_env kenv q_n tmenv) pre

and apply_term : type dom modality mode n m.
    (mode, kinetic) value ->
    (dom, modality, mode, n, m) Modality.filter_dim ->
    (n, (dom, kinetic) value) CubeOf.t ->
    (mode, kinetic) value =
 fun fn filter arg ->
  let (Val v) = apply fn filter arg in
  v

and apply_binder_term : type dom modality mode k n.
    (mode, modality, dom, n, kinetic) binder ->
    (dom, modality, mode, k, n) Modality.filter_dim ->
    (k, (dom, kinetic) value) CubeOf.t ->
    (mode, kinetic) value =
 fun b filter arg ->
  let (Val v) = apply_binder b filter arg in
  v

and force_eval : type mode s. (mode, s) lazy_eval -> (mode, s) evaluation =
 fun lev ->
  let undefer tm s c apps =
    (* TODO: In an ideal world, there would be one function that would traverse the term once doing both "eval" and "act" by the insertion. *)
    let etm = act_evaluation tm s c in
    let etm = app_eval_apps etm apps in
    lev := Ready etm;
    etm in
  match !lev with
  | Deferred_eval (env, tm, ins, c, apps) ->
      let (To p) = deg_of_ins ins in
      undefer (eval env tm) p c apps
  | Deferred (tm, s, c, apps) -> undefer (tm ()) s c apps
  | Ready etm -> etm

and force_eval_term : type mode. (mode, kinetic) lazy_eval -> (mode, kinetic) value =
 fun v ->
  let (Val v) = force_eval v in
  v

(* Apply an 'apps' to something, calling either 'apply' or 'field' or 'inst' for each stage as appropriate. *)
and app_eval_apps : type hmode mode s any.
    (hmode, s) evaluation -> (hmode, mode, any) apps -> (mode, s) evaluation =
 fun ev x ->
  match x with
  | Emp -> ev
  | Arg (rest, filter, xs, ins) -> (
      let mode = Modality.tgt (Modality.filter_modality filter) in
      let (To p) = deg_of_ins ins in
      match app_eval_apps ev rest with
      | Val tm -> act_evaluation (apply tm filter (val_of_norm_cube xs)) p (Modalcell.id2 mode)
      | Realize tm ->
          let (Val v) =
            act_evaluation (apply tm filter (val_of_norm_cube xs)) p (Modalcell.id2 mode) in
          Realize v
      | Unrealized -> Unrealized)
  | Field (rest, filter, fld, fldplus, ins) -> (
      let fm = Modality.filter_modality filter in
      let mode = Modality.tgt fm in
      let (To p) = deg_of_ins ins in
      match app_eval_apps ev rest with
      | Val tm ->
          act_evaluation
            (field fm tm fld (id_ins (cod_left_ins ins) fldplus))
            p (Modalcell.id2 mode)
      | Realize tm ->
          let (Val v) =
            act_evaluation
              (field fm tm fld (id_ins (cod_left_ins ins) fldplus))
              p (Modalcell.id2 mode) in
          Realize v
      | Unrealized -> Unrealized)
  | Inst (rest, _, args) -> (
      match app_eval_apps ev rest with
      | Val tm -> Val (inst tm args)
      | Realize tm -> Realize (inst tm args)
      | Unrealized -> Unrealized)

(* Look up a cube of values in an environment by variable index, accumulating operator actions, shifts, and keys as we go.  At the end, we usually use the operator to select a value from the cubes (with its face part) and act on it (with its degeneracy part).  We assume all the keys on the end of the environment have already been stripped off, even though the input types don't statically rule out a key with identity domain. *)
and lookup_cube : type dom mu munu mode n a b k mk nk.
    (mode, n, b) env ->
    (n, k, nk) D.plus ->
    (dom, mu, mode) Modality.t ->
    (dom, munu, mode) Modality.t ->
    (a, mu, k, b) insert ->
    (mk, nk) opt_op ->
    (dom, mk) looked_up_cube =
 fun env nk mu pretr v op ->
  let n = dim_env env in
  match env with
  (* Since there's an index, the environment can't be empty. *)
  | Emp _ -> (
      match v with
      | _ -> .)
  (* If we encounter an operator action, we accumulate it. *)
  | Act (env, op') ->
      let (Plus lk) = D.plus (D.plus_right nk) in
      let op'k = opt_op_plus op' lk nk in
      lookup_cube env lk mu pretr v (comp_opt_op op'k op)
  (* Keys are disallowed here, because we've already called restrict_keys that is supposed to strip them all off. *)
  | Key (env, cell, plus) -> (
      match (Modalcell.compare_id cell, plus) with
      | Eq, Plus_lock (Zero _, Zero) -> lookup_cube env nk mu pretr v op
      | _ -> fatal (Anomaly "nonidentity key in lookup_cube"))
  (* A prekey doesn't change the codomain context, so it can appear between the values of an environment and thus not be stripped off by restrict_keys.  We accumulate its cell into the returned prekey action.  Since the prekey acts at the environment's mode, but the looked-up value is at its own (deeper) mode, we prewhisker the cell by the transport modality (the vertical target of the composite key returned by restrict_keys), moving its source to the value's mode so that it composes with the accumulated action there. *)
  | Prekey (env, cell) ->
      let (Looked_up { act; op; entry; pre }) = lookup_cube env nk mu pretr v op in
      let (Wrap cell) = Modalcell.prewhisker_wrapped cell pretr in
      let (Prekey_action pre) = prekey_vcomp cell pre in
      Looked_up { act; op; entry; pre }
  (* If we encounter a shift or unshift, we just have to edit the insertion and go on. *)
  | Shift (env, n_x, xb) ->
      (* In this branch, k is renamed to x+k. *)
      let n_xk = nk in
      let (Uncoinsert (y_k, filter_y_x, v, _)) = Plusmap.uncoinsert v xb in
      let x = D.plus_right n_x in
      let (Plus n_y) = D.plus (Modality.filtered x filter_y_x) in
      let yenv =
        act_env env
          (plus_opt_op n n_x n_y (opt_op_of_opt_sface (Modality.sface_of_filter x filter_y_x)))
      in
      let ny_k = D.plus_assocl n_y y_k n_xk in
      lookup_cube yenv ny_k mu pretr v op
  | Unshift (env, n_x, xb) ->
      (* In this branch, n is renamed to n+x. *)
      let nx = n in
      let n = D.plus_left n_x nx in
      let nx_k = nk in
      let (Uninsert (y_k, filter_y_x, v, _)) = Plusmap.uninsert v xb in
      let x = D.plus_right n_x in
      let (Plus n_y) = D.plus (Modality.filtered x filter_y_x) in
      let k = D.plus_right nx_k in
      let (Plus ny_k) = D.plus k in
      let n_yk = D.plus_assocr n_y y_k ny_k in
      let op' = plus_opt_op n n_y n_x (opt_op_of_deg (Modality.deg_of_filter x filter_y_x)) in
      let op'' = opt_op_plus op' ny_k nx_k in
      lookup_cube env n_yk mu pretr v (comp_opt_op op'' op)
  (* If the environment is permuted, we apply the permutation to the index. *)
  | Permute (p, env) ->
      let (Permute_insert (v, _)) = permute_insert v p in
      lookup_cube env nk mu pretr v op
  | Ext { env; plus = mk; values; filter = filter_m_n; filtered = filter_k_k } -> (
      let modality = Modality.filter_modality filter_m_n in
      match v with
      (* If we encounter a variable that isn't ours, we skip it and proceed. *)
      | Later v -> lookup_cube env nk mu pretr v op
      (* Finally, when we find our variable, we decompose the accumulated operator into a strict face and degeneracy, use the face as an index lookup, and act by the degeneracy.  The forcing function is the identity if the entry is not lazy, and force_eval_term if it is lazy. *)
      | Now -> (
          let filter = Modality.filter_plus mk nk filter_m_n filter_k_k in
          let op =
            comp_opt_op (opt_op_of_deg (Modality.deg_of_filter (D.plus_out n nk) filter)) op in
          (* The looked-up value lives at the modality's domain mode, where the prekey action starts as an identity. *)
          let pre = Modalcell.id2 (Modality.src mu) in
          match (values, Modality.compare modality mu) with
          (* Looking up a variable that's bound to an error immediately fails with that error.  (In particular, this sort of failure can't currently happen "deeper" inside a term.) *)
          | `Error e, _ -> fatal e
          | `Ok entry, Eq -> Looked_up { act = (fun x s c -> act_value x s c); op; entry; pre }
          | `Lazy entry, Eq ->
              Looked_up
                { act = (fun x s c -> force_eval_term (act_lazy_eval x s c)); op; entry; pre }
          | _, Neq -> fatal (Modality_mismatch (`Internal, "lookup_cube keys", modality, mu))))

and lookup : type mode n b. (mode, n, b) env -> (mode, b) index -> (mode, kinetic) value =
 fun env (Index (v, fa, _, (Plus_with_locks (_, locks) as plus))) ->
  let (Plus n_k) = D.plus (cod_sface fa) in
  let n = dim_env env in
  (* We strip off the keys and prekeys corresponding to the locks to the right of the variable, composing them on the way out into a composite key cell (for the variable's own locks) and a prekey action, both to be applied to the looked-up value.  The prekeys encountered inside the environment by lookup_cube are transported to the value's mode by prewhiskering with the vertical target of the composite key. *)
  let (Restrict_keys (env, extra, _, keys, pre)) = restrict_keys env plus in
  match (extra, v) with
  (* The extension of an index includes all the locks to the right of the variable, and a key can only span locks, so the split can never land in the middle of a key here. *)
  | Plus_lock (Suc _, _), _ -> .
  | Plus_lock (Zero _, Zero), _ -> (
      let mu = Locks.cod locks in
      match lookup_cube env n_k mu (Modalcell.vtgt keys) v (id_opt_op (D.plus_out n n_k)) with
      | Looked_up { act; op; entry; pre = inner_pre } -> (
          let (Plus x) = D.plus (dom_sface fa) in
          match op_of_opt (comp_opt_op op (plus_opt_op n n_k x (opt_op_of_sface fa))) with
          | Some (Op (f, s)) ->
              (* We combine, into a single cell applied in one traversal, the composite lock keys (innermost), then the prekey action from inside the environment, then the prekey action from the stripped-off extension (outermost). *)
              let (Prekey_action c) = prekey_vcomp inner_pre keys in
              let (Prekey_action c) = prekey_vcomp pre c in
              act (CubeOf.find entry f) s c
          (* This means that in the non-unary case, some dummy endpoints in an opt_sface didn't get canceled out by a degeneracy.  I think that could only happen if a non-unary mode theory has a 2-cell from a sharp parametric modality to a sharp non-parametric modality.  In all the models I know, the primary nonparametric modalities are *comonadic*, plus in the unary case *only* a left adjoint monad to it (which is also right adjoint if the parametricity is internal), and in the external non-unary case another non-monadic non-comonadic functor.  In the internal non-unary case there is a *right* adjoint to the nonparametric comonad, but it is not "nonparametric" in this sense: its parametricity is *codiscrete* rather than discrete; I haven't thought about how to enforce that for a tangible modality, although it comes naturally for a negative presentation that is right adjoint to a tangible discrete modality. *)
          | None -> fatal (Invalid_mode_theory "uncanceled dummy endpoints")))

(* Instantiate an arbitrary value, combining tubes. *)
and inst : type mode m n mn s.
    (mode, s) value -> (m, n, mn, mode normal) TubeOf.t -> (mode, s) value =
 fun tm args2 ->
  let n = TubeOf.inst args2 in
  match D.compare_zero n with
  | Zero -> tm
  | Pos dim2 -> (
      match view_term tm with
      | Neu { head; args = neu_args; value; ty = (lazy ty) } -> (
          (* We have to combine the new instantiation with any existing instantation at the end of the application spine. *)
          let base_args, args1 = inst_of_apps neu_args in
          let (Any_tube args1) =
            Option.value args1 ~default:(Any_tube (TubeOf.empty (TubeOf.out args2))) in
          match D.compare (TubeOf.out args2) (TubeOf.uninst args1) with
          | Neq ->
              fatal
                (Dimension_mismatch ("instantiating a type 1", TubeOf.out args2, TubeOf.uninst args1))
          | Eq -> (
              let (Plus nk) = D.plus (TubeOf.inst args1) in
              let newargs = TubeOf.plus_tube nk args1 args2 in
              let args = Inst (base_args, D.pos_plus dim2 nk, newargs) in
              (* Now we have to construct the type OF the new instantiation.  The old term must have belonged to some instantiation of the universe of the previously uninstantiated dimension. *)
              match view_type ty "inst" with
              | Canonical (_, UU (mode, m), ins, tys1) -> (
                  let Eq = eq_of_ins_zero ins in
                  match D.compare m (TubeOf.uninst args1) with
                  | Neq ->
                      fatal (Dimension_mismatch ("instantiating a type 2", m, TubeOf.uninst args1))
                  | Eq ->
                      let value = inst_lazy mode value args2 in
                      let ty = lazy (tyof_inst mode tys1 args2) in
                      Neu { head; args; value; ty })
              | _ -> fatal (Anomaly "can't instantiate non-type")))
      | Canonical { mode; canonical = c; tyargs = args1; ins; fields; inst_fields = _ } -> (
          match D.compare (TubeOf.out args2) (TubeOf.uninst args1) with
          | Neq ->
              fatal
                (Dimension_mismatch ("instantiating a type 3", TubeOf.out args2, TubeOf.uninst args1))
          | Eq ->
              let (Plus nk) = D.plus (TubeOf.inst args1) in
              let args = TubeOf.plus_tube nk args1 args2 in
              (* The instantiated fibrancy fields are computed lazily, on demand, by get_fibrancy_fields, which caches them in the mutable inst_fields. *)
              Canonical { mode; canonical = c; tyargs = args; ins; fields; inst_fields = None })
      | Lam _ | Struct _ | Constr _ -> fatal (Anomaly "instantiating non-type"))

(* Instantiate a list of fibrancy fields by passing repeatedly to its internal corecursive 'id' field. *)
and inst_fibrancy_fields : type mode m n mn.
    mode Mode.t ->
    (mode * mn * potential * no_eta) Value.StructfieldAbwd.t ->
    (m, n, mn, mode normal) TubeOf.t ->
    (mode * m * potential * no_eta) Value.StructfieldAbwd.t option =
 fun mode fields tyargs ->
  let open Monad.Ops (Monad.Maybe) in
  match Hott.faces () with
  | None -> None
  | Some (_, _, l) -> (
      match D.compare_zero (TubeOf.inst tyargs) with
      | Zero ->
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.plus_zero (TubeOf.uninst tyargs)) in
          Some fields
      | Pos n -> (
          let m = TubeOf.uninst tyargs in
          let m_n1 = TubeOf.plus tyargs in
          let (Is_suc (n, n_1, one)) = suc_pos n in
          match D.compare (D.plus_right n_1) Hott.dim with
          | Neq -> fatal (Dimension_mismatch ("inst_fibrancy_fields", D.plus_right n_1, Hott.dim))
          | Eq -> (
              let (Plus m_n) = D.plus n in
              let middle, outer = TubeOf.split m_n n_1 tyargs in
              (* TODO: Is it always correct to use the identity fldins? *)
              let mn_1 = D.plus_assocl m_n n_1 m_n1 in
              let fldins = id_ins (D.plus_out m m_n) mn_1 in
              let idfld =
                struct_field ~unset_ok:true "fibrancy" Potential (Modality.id mode) fields
                  Fibrancy.fid fldins in
              let (Snoc (Snoc (Emp, xcube), ycube)) = TubeOf.to_cube_bwv one l outer in
              let v =
                match
                  app_eval_apps idfld
                    (Arg
                       ( Arg
                           ( Emp,
                             Modality.filter_id mode (CubeOf.dim xcube),
                             xcube,
                             ins_zero (CubeOf.dim xcube) ),
                         Modality.filter_id mode (CubeOf.dim ycube),
                         ycube,
                         ins_zero (CubeOf.dim ycube) ))
                with
                | Val v -> Some v
                | Realize (Neu { value; _ }) -> (
                    match force_eval value with
                    | Val v -> Some v
                    | _ -> None)
                | _ -> None in
              match v with
              | Some (Struct { fields; ins; energy = Potential; eta = Noeta }) -> (
                  match (is_id_ins ins, D.compare (cod_left_ins ins) (TubeOf.out middle)) with
                  | Some _, Eq -> inst_fibrancy_fields mode fields middle
                  | Some _, Neq ->
                      fatal
                        (Dimension_mismatch ("inst_fibrancy", cod_left_ins ins, TubeOf.out middle))
                  | None, _ -> fatal (Anomaly "nonidentity insertion on evaluation of fibrancy id"))
              | Some _ -> fatal (Anomaly "fibrancy id didn't yield a struct")
              | None -> Some Emp)))

and get_fibrancy_fields : type mode m k mk e n.
    (mode, m, k, mk, e, n) inst_canonical -> (mode * m * potential * no_eta) Value.StructfieldAbwd.t
    =
 fun c ->
  match c.inst_fields with
  | Some f -> f
  | None -> (
      match inst_fibrancy_fields c.mode c.fields c.tyargs with
      | Some f ->
          c.inst_fields <- Some f;
          f
      | None -> Emp)

(* Given two families of values, the second intended to be the types of the other, annotate the former by instantiations of the latter to make them into normals.  Since we have to instantiate the types at the *normal* version of the terms, which is what we are computing, we also add the results to a hashtable as we create them so we can access them randomly later.  And since we have to do this sometimes with cubes and sometimes with tubes, we first define the content of the operation as a helper function. *)

and norm_of_val : type mode m n.
    (n sface_of, mode normal) Hashtbl.t ->
    (m, n) sface ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    mode normal =
 fun new_tm_tbl fab tm ty ->
  let args =
    TubeOf.build D.zero
      (D.zero_plus (dom_sface fab))
      {
        build = (fun fc -> Hashtbl.find new_tm_tbl (SFace_of (comp_sface fab (sface_of_tface fc))));
      } in
  let ty = inst ty args in
  let newtm = { tm; ty } in
  Hashtbl.add new_tm_tbl (SFace_of fab) newtm;
  newtm

and norm_of_vals_cube : type mode k.
    (k, (mode, kinetic) value) CubeOf.t ->
    (k, (mode, kinetic) value) CubeOf.t ->
    (k, mode normal) CubeOf.t =
 fun tms tys ->
  let new_tm_tbl = Hashtbl.create 10 in
  CubeOf.mmap { map = (fun fab [ tm; ty ] -> norm_of_val new_tm_tbl fab tm ty) } [ tms; tys ]

and norm_of_vals_tube : type mode n k nk.
    (n, k, nk, (mode, kinetic) value) TubeOf.t ->
    (n, k, nk, (mode, kinetic) value) TubeOf.t ->
    (n, k, nk, mode normal) TubeOf.t =
 fun tms tys ->
  let new_tm_tbl = Hashtbl.create 10 in
  TubeOf.mmap
    { map = (fun fab [ tm; ty ] -> norm_of_val new_tm_tbl (sface_of_tface fab) tm ty) }
    [ tms; tys ]

(* Given a type belonging to the m+n dimensional universe instantiated at tyargs, compute the instantiation of the m-dimensional universe that its instantiation belongs to. *)
and tyof_inst : type mode m n mn.
    mode Mode.t ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    (m, n, mn, mode normal) TubeOf.t ->
    (mode, kinetic) value =
 fun mode tyargs eargs ->
  let m = TubeOf.uninst eargs in
  let n = TubeOf.inst eargs in
  let mn = TubeOf.plus eargs in
  let margs =
    TubeOf.build D.zero (D.zero_plus m)
      {
        build =
          (fun fe ->
            let j = dom_tface fe in
            let (Plus jn) = D.plus (D.plus_right mn) in
            let jnargs =
              TubeOf.build j jn
                {
                  build =
                    (fun fa ->
                      let (PFace_of_plus (pq, fc, fd)) = pface_of_plus fa in
                      TubeOf.find eargs
                        (sface_plus_tface
                           (comp_sface (sface_of_tface fe) fc)
                           (D.plus_zero m) mn pq fd));
                } in
            (* We need to able to look things up in tyargs that are indexed by a composite of tfaces.  TODO: Actually define composites of tfaces, with each other and/or with sfaces on one side or the other, so that this works.  For the moment, we punt and use a hashtbl indexed by sfaces. *)
            let tyargtbl = Hashtbl.create 10 in
            TubeOf.miter
              { it = (fun fa [ ty ] -> Hashtbl.add tyargtbl (SFace_of (sface_of_tface fa)) ty) }
              [ tyargs ];
            let jntyargs =
              TubeOf.build D.zero
                (D.zero_plus (D.plus_out j jn))
                {
                  build =
                    (fun fa ->
                      let fb = sface_plus_sface (sface_of_tface fe) mn jn (id_sface n) in
                      Hashtbl.find tyargtbl (SFace_of (comp_sface fb (sface_of_tface fa))));
                } in
            let tm = inst (TubeOf.find tyargs (tface_plus fe mn mn jn)).tm jnargs in
            let ty = tyof_inst mode jntyargs jnargs in
            { tm; ty });
      } in
  inst (universe mode m) margs

(* Apply a function to all the values in a cube one by one as 0-dimensional applications, rather than as one n-dimensional application. *)
let apply_singletons : type dom modality mode n.
    (dom, modality, mode) Modality.t ->
    (mode, kinetic) value ->
    (n, (dom, kinetic) value) CubeOf.t ->
    (mode, kinetic) value =
 fun modality fn xs ->
  let filter = Modality.filter_zero modality in
  let module MC = CubeOf.Monadic (Monad.State (struct
    type t = (mode, kinetic) value
  end))
  in
  snd
    (MC.miterM
       { it = (fun _ [ x ] fn -> ((), apply_term fn filter (CubeOf.singleton x))) }
       [ xs ] fn)

let apply_singleton_nfs : type dom modality mode n.
    (dom, modality, mode) Modality.t ->
    (mode, kinetic) value ->
    (n, dom normal) CubeOf.t ->
    (mode, kinetic) value =
 fun modality fn xs ->
  let filter = Modality.filter_zero modality in
  let module MC = CubeOf.Monadic (Monad.State (struct
    type t = (mode, kinetic) value
  end))
  in
  snd
    (MC.miterM
       { it = (fun _ [ x ] fn -> ((), apply_term fn filter (CubeOf.singleton x.tm))) }
       [ xs ] fn)

let apply_singleton_tube_nfs : type dom modality mode n.
    (dom, modality, mode) Modality.t ->
    (mode, kinetic) value ->
    (D.zero, n, n, dom normal) TubeOf.t ->
    (mode, kinetic) value =
 fun modality fn xs ->
  let filter = Modality.filter_zero modality in
  let module MC = TubeOf.Monadic (Monad.State (struct
    type t = (mode, kinetic) value
  end))
  in
  snd
    (MC.miterM
       { it = (fun _ [ x ] fn -> ((), apply_term fn filter (CubeOf.singleton x.tm))) }
       [ xs ] fn)

(* Evaluate a term context to produce a value context. *)

let eval_bindings : type dom modality mode a b n bm.
    (mode, a, b) Ctx.Ordered.t ->
    (dom, modality, mode, n, n) Modality.filter_dim ->
    ((b, (modality, n) dim_entry) snoc, mode, modality, dom, bm) plus_lock ->
    (n, (dom, bm) binding) CubeOf.t ->
    (n, dom Ctx.Binding.t) CubeOf.t =
 fun ctx filter al cbs ->
  let i = Ctx.Ordered.length ctx in
  let vbs = CubeOf.build (CubeOf.dim cbs) { build = (fun _ -> Ctx.Binding.unknown ()) } in
  let ctx = Ctx.Ordered.invis ctx filter vbs in
  let modality = Modality.filter_modality filter in
  let tempctx = Ctx.Ordered.lock_to ctx modality al in
  let argtbl = Hashtbl.create 10 in
  let j = ref 0 in
  let () =
    CubeOf.miter
      {
        it =
          (fun fa [ ({ ty = cty; tm = ctm } : (dom, bm) binding); vb ] ->
            (* Unlike in dom_vars, we don't need to instantiate the types, since their instantiations should have been preserved by readback and will reappear correctly here. *)
            let ety = eval_term (Ctx.Ordered.env tempctx) cty in
            let level = (i, !j) in
            j := !j + 1;
            let lvl, v =
              match ctm with
              | None -> (Some level, ({ tm = var modality level ety; ty = ety } : dom normal))
              | Some ctm -> (None, { tm = eval_term (Ctx.Ordered.env tempctx) ctm; ty = ety }) in
            Hashtbl.add argtbl (SFace_of fa) v;
            Ctx.Binding.specify vb lvl v);
      }
      [ cbs; vbs ] in
  vbs

let eval_entry : type dom modality mode a b f n bm.
    (mode, a, b) Ctx.Ordered.t ->
    (dom, modality, mode, b, bm, f, n) entry ->
    (dom, modality, mode, f, n) Ctx.entry =
 fun ctx e ->
  match e with
  | Vis { dim; plus_lock; filter; plusdim; vars; bindings; hasfields; fields; fplus } ->
      let bindings = eval_bindings ctx filter plus_lock bindings in
      let fields = Bwv.map (fun (f, x, _) -> (f, x)) fields in
      Vis { dim; filter; plusdim; vars; bindings; hasfields; fields; fplus }
  | Invis { plus_lock; bindings; filter; _ } ->
      Invis { filter; bindings = eval_bindings ctx filter plus_lock bindings }

let rec eval_ordered_ctx : type mode a b. (mode, a, b) ordered_termctx -> (mode, a, b) Ctx.Ordered.t
    = function
  | Emp mode -> Emp mode
  | Ext (ctx, e, af) ->
      let ectx = eval_ordered_ctx ctx in
      Snoc (ectx, eval_entry ectx e, af)
  | Lock (ctx, lock) -> Lock (eval_ordered_ctx ctx, lock)
  | Weaken (ctx, code) -> Weaken (eval_ordered_ctx ctx, code)

let eval_ctx : type mode a b. (mode, a, b) termctx -> (mode, a, b) Ctx.t = function
  | Permute (perm, ctx) ->
      let ctx = eval_ordered_ctx ctx in
      Permute { perm; env = Ctx.Ordered.env ctx; level = Ctx.Ordered.length ctx; ctx }

(* Evaluate a telescope (forwards context of terms) and append the result to a context. *)
let rec eval_append : type mode a b c ac bc.
    (mode, a, b) Ctx.t ->
    (a, c, ac) Fwn.bplus ->
    (mode, b, c, bc) Telescope.t ->
    (mode, ac, bc) Ctx.t =
 fun ctx ac tel ->
  match (ac, tel) with
  | Zero, Emp -> ctx
  | Suc ac, Ext (x, Modal (modality, al, ty), tel) ->
      let lctx = Ctx.lock_to ctx modality al in
      let ty = eval_term (Ctx.env lctx) ty in
      eval_append (Ctx.ext ctx modality x ty) ac tel

(* Get the instantiation arguments of a type, of any sort. *)
let get_tyargs : type mode.
    ?severity:Asai.Diagnostic.severity -> (mode, kinetic) value -> string -> mode normal TubeOf.full
    =
 fun ?(severity = Asai.Diagnostic.Bug) ty err ->
  match view_type ~severity ty err with
  | Canonical (_, _, _, tyargs) -> Full_tube tyargs
  | Neutral (_, _, tyargs) -> Full_tube tyargs

(* Check whether a given type is discrete, or has one of the the supplied constant heads (since for testing whether a newly defined datatype can be discrete, it and members of its mutual families can appear in its own parameters and arguments). *)
let is_discrete : type mode. ?discrete:unit Constant.Map.t -> (mode, kinetic) value -> bool =
 fun ?discrete ty ->
  match (view_type ty "is_discrete", discrete) with
  | Canonical (_, Data { discrete = `Yes; _ }, _, _), _ -> true
  (* The currently-being-defined types may not be known to be discrete yet, but we treat them as discrete if they are one of the given heads. *)
  | Canonical (Const { name; ins }, _, _, _), Some consts ->
      Option.is_some (is_id_ins ins) && Constant.Map.mem name consts
  | Neutral (Const { name; ins }, _, _), Some consts ->
      Option.is_some (is_id_ins ins) && Constant.Map.mem name consts
      (* In theory, pi-types with discrete codomain, and record types with discrete fields, could also be discrete.  But that would be trickier to check as it would require evaluating their codomain and fields under binders, and eta-conversion for those types should implement direct discreteness automatically.  So the only thing we're missing is that they can't appear as arguments to a constructor of some other discrete datatype. *)
  | _ -> false

let () =
  View.term_viewer := { view = view_term };
  View.type_viewer := { view = view_type };
  View.eval_forcer := { force = force_eval }
