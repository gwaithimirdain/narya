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

(* Since some entries in an environment are lazy and some aren't, lookup_cube returns a cube whose entries belong to an existential type, along with a function to act on any element of that type and force it into a value.  It also returns an accumulated operator by which to act, first selecting an entry in the cube with a face and then acting on that value by a degeneracy, and the horizontal composite of all the keys it passed through on the way to the entry. *)
(* The result of looking up a cube of values in an environment.  The lookup is built up on the *return* path of the recursion (see lookup_cube), so that we only ever push operators and shifts *along* a filter in the degeneracy direction (with filter_op, filter_comp, deg_of_filter), never in the section direction; this avoids needing to choose endpoints to fill in filtered-away directions, so that it works even in a theory with no endpoints.

   The 'op and 'filter concern only the dimension of the *environment* (not the intrinsic dimension 'k of the cube variable); the latter is carried separately by 'filtered and 'plus, and recombined with the variable's own face only at the very end in lookup.  This is what lets the recursion mirror replace_keys_rec exactly, with no need to extend any filter or operator across the intrinsic dimension when crossing a key.

   'filter (by the partial composite 'sigma of the keys consumed so far) relates the environment dimension 'n at this level to the dimension 'm at which the op acts; 'op relates 'm to the filtered environment-part 'mfilt of the entry cube; 'filtered and 'plus express that the entry cube has dimension 'mfilt + 'k, with the intrinsic part 'k left fixed by the variable's modality 'mu. *)
type (_, _, _, _, _, _, _) looked_up_cube =
  | Looked_up : {
      act :
        'x 'y 'mu2 'nu2 'cod2.
        'a ->
        ('x, 'y) deg ->
        ('mode, 'mu2, 'nu2, 'cod2) Modalcell.t option ->
        ('mode, kinetic) value;
      op : ('m, 'mfilt) op;
      filter : ('mode, 'sigma, 'mcur, 'm, 'n) Modality.filter_dim;
      filtered : ('mode, 'mu, 'cod, 'k, 'k) Modality.filter_dim;
      plus : ('mfilt, 'k, 'nentry) D.plus;
      entry : ('nentry, 'a) CubeOf.t;
      cell : ('mode, 'cod) Modalcell.wrapped;
    }
      -> ('mode, 'sigma, 'mcur, 'cod, 'mu, 'k, 'n) looked_up_cube

(* Require that the supplied list contains exactly one argument for each annotated variable being added, and add all of those cubes to the given environment. *)
let rec take_args : type mode annotations m n mn a b ab.
    (mode, m, a) env ->
    (m, n, mn) D.plus ->
    (mn, mode, kinetic) modal_value_cube list ->
    (n, mode, annotations, mode, mode, b, mode) VarAnnotate.fwd_t ->
    (mode, b, mode, a, unit, ab) Tctx.bcomp ->
    (mode, m, ab) env =
 fun env mn dargs annotate comp ->
  match (dargs, annotate, comp) with
  | [], Zero _, Zero -> env
  | Modal (mu, fmn, arg) :: args, Suc (Annotate (amu, fn), annotate), Suc (Dim _, comp) -> (
      match Modality.compare mu amu with
      | Eq ->
          let (Filter_of_plus (ij, fm, fn2)) = Modality.filter_of_plus mn fmn in
          let Eq = Modality.filter_uniq fn2 fn in
          let env =
            Ext
              {
                env;
                plus = ij;
                modality = mu;
                filter = fm;
                filtered = Modality.filter_idempotent fn;
                values = `Ok arg;
              } in
          take_args env mn args annotate comp
      | Neq -> fatal (Modality_mismatch (`Internal, "take_args", mu, amu)))
  | _ -> fatal (Anomaly "wrong number of arguments in argument list")

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
                            eval_term (act_env env (op_of_sface (sface_of_tface fa))) (Const name)
                          in
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
                       (act_env env (op_of_sface (sface_of_tface fa)))
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
                    let tm = eval_term (act_env env (op_of_sface fb)) (TubeOf.find args fcd) in
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
  | Lam (Variables (n, n_k, vars), modality, p, filter, body) ->
      let m = dim_env env in
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
  | App (fn, Modal (modality, al, args)) ->
      (* First we evaluate the function. *)
      let efn = eval_term env fn in
      (* The environment is m-dimensional and the original application is n-dimensional, so the *substituted* application is m+n dimensional.  Thus must therefore match the dimension of the function being applied. *)
      let m = dim_env env in
      let n = CubeOf.dim args in
      (* Then we evaluate all the arguments, not just in the given environment (of dimension m), but in that environment acted on by all the strict faces of m.  Since the given arguments are indexed by strict faces of n, the result is a collection of values indexed by strict faces of m+n.  Furthermore, we have to filter m by the modality first.  *)
      let (Has_filter filter) = Modality.filter modality m in
      let k = Modality.filtered m filter in
      let (Plus k_n) = D.plus n in
      let kn = D.plus_out k k_n in
      let lenv = key_env env filter (Modalcell.id modality) al in
      let eargs = eval_args lenv k_n kn args in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      apply efn modality eargs
  | Field (tm, fld, fldins) ->
      let m = dim_env env in
      let n, l = (dom_ins fldins, cod_left_ins fldins) in
      let Plus m_n, Plus m_l = (D.plus n, D.plus l) in
      field (eval_term env tm) fld (plus_ins m m_n m_l fldins)
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
          (fun (Term.Modal (modality, lfilter, al, tm)) ->
            let (Has_filter kfilter) = Modality.filter modality m in
            let k = Modality.filtered m kfilter in
            let (Plus k_l) = D.plus (Modality.filtered n lfilter) in
            let kl = D.plus_out k k_l in
            let filter = Modality.filter_plus k_l m_n kfilter lfilter in
            let lenv = key_env env kfilter (Modalcell.id modality) al in
            Value.Modal (modality, filter, eval_args lenv k_l kl tm))
          args in
      Val (Constr (constr, mn, eargs))
  | Pi
      (type l n dom modality)
      ({ x; filter = lfilter; doms; cods } : (l, n, dom, modality, mode, b) pi_args) ->
      let (Term.Modal (modality, al, doms)) = doms in
      (* We are starting with an n-dimensional pi-type and evaluating it in an m-dimensional environment, producing an (m+n)-dimensional result. *)
      let l, n = (CubeOf.dim doms, CodCube.dim cods) in
      let m = dim_env env in
      let (Has_filter (type k) (kfilter : (dom, modality, mode, k, m) Modality.filter_dim)) =
        Modality.filter modality m in
      (* We filter the dimension m by the modality, and that is what gets added to the dimension of the domains. *)
      let k = Modality.filtered m kfilter in
      let (Plus (type kl) (k_l : (k, l, kl) D.plus)) = D.plus l in
      let kl = D.plus_out k k_l in
      let (Plus (type mn) (m_n : (m, n, mn) D.plus)) = D.plus n in
      let mn = D.plus_out m m_n in
      let filter = Modality.filter_plus k_l m_n kfilter lfilter in
      (* The basic thing we do is evaluate the cubes of domains and codomains. *)
      let lenv = key_env env kfilter (Modalcell.id modality) al in
      let doms =
        CubeOf.build kl
          {
            build =
              (fun fab ->
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus k_l fab in
                eval_term (act_env lenv (op_of_sface fa)) (CubeOf.find doms fb));
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
                BindFam (eval_binder (act_env env (op_of_sface fa)) i_j modality jfilter1 x));
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
        let head : mode head =
          Pi { x = subx; modality; filter = ufilter; doms = subdoms; cods = subcods } in
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
                          modality;
                          filter;
                          filtered = Modality.filter_zero modality;
                          values = `Ok doms;
                        };
                    plus = D.plus_zero mn;
                    modality = Modality.id codmode;
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
                    canonical =
                      Pi { x = subx; modality; filter = ufilter; doms = subdoms; cods = subcods };
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
      let lenv = key_env env fm (Modalcell.id modality) al in
      eval
        (Ext
           {
             env;
             plus = D.plus_zero k;
             modality;
             filter = fm;
             filtered = Modality.filter_zero modality;
             values =
               `Lazy
                 (CubeOf.build k
                    { build = (fun fa -> lazy_eval (act_env lenv (op_of_sface fa)) v) });
           })
        body
  (* It's tempting to write just "act_value (eval env x) s" here, but that is WRONG!  Pushing a substitution through an operator action requires whiskering the operator by the dimension of the substitution. *)
  | Act (x, s, _) ->
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg s) in
      let (Plus kn) = D.plus (cod_deg s) in
      let ks = plus_deg k kn km s in
      (* We push as much of the resulting degeneracy into the environment as possible, in hopes that the remaining insertion outside will be trivial and act_value will be able to short-circuit.  (Ideally, the insertion would be carried through by eval for a single traversal in all cases.) *)
      let (Insfact (fa, ins)) = insfact ks kn in
      let (To p) = deg_of_ins ins in
      Val (act_value (eval_term (act_env env (op_of_deg fa)) x) p None)
  | Key { tm; cell; plus_src; plus_tgt } ->
      (* To evaluate a key, we replace the keys in the environment corresponding to the codomain of the key cell by their composite with the supplied cell, producing an environment for evaluating the body. *)
      eval (Env.replace_keys env plus_tgt cell plus_src) tm
  | Match { tm; dim = match_dim; branches } -> (
      let env_dim = dim_env env in
      let (Plus plus_dim) = D.plus match_dim in
      let total_dim = D.plus_out env_dim plus_dim in
      (* Get the argument being inspected *)
      match view_term (eval_term env tm) with
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
              match D.compare constr_dim total_dim with
              | Neq -> fatal (Dimension_mismatch ("evaluating match", constr_dim, total_dim))
              | Eq ->
                  (* If we have a branch with a matching constructor, then our constructor must be applied to exactly the right number of elements (in dargs).  In that case, we pick them out and add them to the environment. *)
                  let env = take_args env plus_dim dargs annotate comp in
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
          eval (Act (env, op)) tm)
  | Shift (n, plusmap, tm) ->
      let (Plus mn) = D.plus n in
      eval (Unshift (env, mn, plusmap)) tm
  | Weaken tm -> eval (Env.remove_top env) tm

and eval_with_boundary : type mode m a.
    (mode, m, a) env -> (mode, a, kinetic) term -> (m, (mode, kinetic) value) CubeOf.t =
 fun env tm ->
  CubeOf.build (dim_env env) { build = (fun fa -> eval_term (act_env env (op_of_sface fa)) tm) }

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
          eval_term (act_env env (op_of_sface fa)) (CubeOf.find tms fb));
    }

(* Apply a function value to an argument (with its boundaries). *)
and apply : type dom modality mode n s.
    (mode, s) value ->
    (dom, modality, mode) Modality.t ->
    (n, (dom, kinetic) value) CubeOf.t ->
    (mode, s) evaluation =
 fun fn modality arg ->
  match view_term fn with
  (* If the function is a lambda-abstraction, we check that it has the correct dimension and mode and then beta-reduce, adding the arguments to the environment. *)
  | Lam (_, _, body) -> (
      let m = dim_binder body in
      let bmod = modality_binder body in
      let (Has_filter filter) = Modality.filter bmod m in
      let n = CubeOf.dim arg in
      match (D.compare (Modality.filtered m filter) n, Modality.compare bmod modality) with
      | Eq, Eq -> apply_binder body filter arg
      | Neq, _ -> fatal (Dimension_mismatch ("applying a lambda", m, n))
      | _, Neq -> fatal (Modality_mismatch (`Internal, "applying a lambda", bmod, modality)))
  (* If it is a uninstantiated neutral application... *)
  | Neu { head; args; value; ty = (lazy ty) } -> (
      (* ... we check that its type is fully instantiated... *)
      match view_type ty "apply" with
      | Canonical (_, Pi { modality = pi_modality; filter; doms; cods; _ }, ins, tyargs) -> (
          (* ... and that the pi-type and its instantiation have the correct dimension. *)
          let k = CubeOf.dim doms in
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
              let args = Arg (args, modality, newarg, ins_zero k) in
              if GluedEval.read () then
                (* We add the argument to the lazy value and return a glued neutral. *)
                let value = apply_lazy value modality newarg in
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
                           Data { dim; tyfam; indices = Unfilled _ as indices; constrs; discrete };
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
                                 canonical = Data { dim; tyfam; indices; constrs; discrete };
                                 tyargs = TubeOf.empty dim;
                                 ins;
                                 fields;
                                 inst_fields = None;
                               }) in
                        Val (Neu { head; args; value = ready value; ty = newty }))
                | Val tm -> (
                    let value = apply tm modality arg in
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
  (* TODO: These idempotents seem wrong.  It's BindFam that's forcing the parameter dimension of its binders to be already filtered, but they aren't filtered when created. *)
  let out_args =
    TubeOf.mmap
      {
        map =
          (fun fa [ { tm = afn; ty = _ } ] ->
            let fa = sface_of_tface fa in
            let (Filter_sface (fb, bf1)) = Modality.filter_sface filter fa in
            let tmargs = CubeOf.subcube fb args in
            let (BindFam b) = BindCube.find cods fa in
            let tm = apply_term afn (modality_binder b) tmargs in
            let cod = apply_binder_term b bf1 tmargs in
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

(* Compute a field of a structure (or a fibrant type). *)
and field : type mode n k nk s.
    (mode, s) value -> k Field.t -> (nk, n, k) insertion -> (mode, s) evaluation =
 fun tm fld fldins ->
  match view_term tm with
  | Struct { fields; ins = structins; energy; eta = _ } -> (
      match (is_id_ins structins, D.compare (cod_left_ins structins) (dom_ins fldins)) with
      | Some _, Eq -> struct_field "struct" energy fields fld fldins
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
      | Eq -> struct_field "canonical" Potential fields fld fldins)
  | viewed_tm -> (
      (* We push the permutation from the insertion inside. *)
      let n, k = (cod_left_ins fldins, cod_right_ins fldins) in
      let (Plus fldplus) = D.plus k in
      let p = deg_of_perm (perm_inv (perm_of_ins_plus fldins fldplus)) in
      match act_value viewed_tm p None with
      (* It must be an uninstantiated neutral application (which could be either an element of a record/codata, or a fibrant type). *)
      | Neu { head; args; value; ty = (lazy ty) } -> (
          let newty = lazy (tyof_field (Ok tm) ty fld ~shuf:Trivial fldins) in
          let args = Field (args, fld, fldplus, ins_zero n) in
          if GluedEval.read () then
            let value = field_lazy value fld fldins in
            Val (Neu { head; args; value; ty = newty })
          else
            match force_eval value with
            | Unrealized -> Val (Neu { head; args; value = ready Unrealized; ty = newty })
            | Val tm -> (
                (* At this point we've already pushed the insertion inside in computing our neutral, so the remaining insertion on the field to compute of its value is "the identity" of appropriate dimensions *)
                let value = field tm fld (ins_of_plus n fldplus) in
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

and struct_field : type mode s et n k nk.
    ?unset_ok:bool ->
    string ->
    s energy ->
    (mode * nk * s * et) StructfieldAbwd.t ->
    k Field.t ->
    (nk, n, k) insertion ->
    (mode, s) evaluation =
 fun ?(unset_ok = false) err energy fields fld fldins ->
  match StructfieldAbwd.find_opt fields fld with
  | Found (Lower (v, _)) -> force_eval v
  | Found (Higher (lazy { vals; intrinsic; _ })) -> (
      match D.compare intrinsic (cod_right_ins fldins) with
      | Eq -> (
          match InsmapOf.find fldins vals with
          | Some v -> force_eval v
          | None -> if unset_ok then Unrealized else fatal (Anomaly (err ^ " field value unset")))
      | Neq ->
          fatal (Dimension_mismatch (err ^ " field intrinsic", intrinsic, cod_right_ins fldins)))
  | _ -> (
      match energy with
      | Potential -> Unrealized
      | Kinetic -> fatal (Anomaly ("missing field in eval struct: " ^ Field.to_string fld)))

and field_term : type mode n k nk.
    (mode, kinetic) value -> k Field.t -> (nk, n, k) insertion -> (mode, kinetic) value =
 fun x fld fldins ->
  let (Val v) = field x fld fldins in
  v

(* Given a term and its record type, compute the type of a field projection, and the substitution dimension it was evaluated at.  There are two versions of this function, one for when we already know the insertion associated to the field, and one for when we are synthesizing it from the user's integer sequence.  First we define the shared part of both, where we have already found the codatafield from the codata type.  We allow the term to be an error, in case typechecking failed earlier but we are continuing on; this can nevertheless succeed (or fail in more interesting ways) if the type doesn't actually depend on that value. *)

and tyof_codatafield : type mode m n mn a k r s i et.
    ((mode, kinetic) value, Code.t) Result.t ->
    i Field.t ->
    (i, mode * a * n * et) Codatafield.t ->
    (mode, m, a) env ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    m D.t ->
    (m, n, mn) D.plus ->
    (* We allow passing through a shuffle and eval-readback as well, in the case that this is a higher field being called recursively as part of the instantiation arguments. *)
    shuf:(mode, r, k, i, a) shuffleable ->
    (m, s, k) insertion ->
    (mode, kinetic) value =
 fun tm fldname fldty env tyargs m mn ~shuf fldins ->
  (* The type of the field projection comes from the type associated to that field name in general, evaluated at the stored environment extended by the term itself and its boundaries. *)
  match fldty with
  | Term.Codatafield.Lower fldty -> tyof_lower_codatafield tm fldname fldty env tyargs m mn
  | Term.Codatafield.Higher (ic0, fldty) ->
      let Eq = D.plus_uniq mn (D.plus_zero m) in
      tyof_higher_codatafield tm fldname env tyargs fldins ic0 fldty ~shuf

(* We dispatch to separate helper functions for lower fields and higher fields that assume all the dimensions are correct.  These helper functions can be called directly by a caller who knows that all the dimensions are correct, such as check_field where the field is obtained by iterating directly through the codatatype. *)
and tyof_lower_codatafield : type mode m n mn a.
    ((mode, kinetic) value, Code.t) Result.t ->
    D.zero Field.t ->
    (mode, (a, (mode id, n) dim_entry) snoc, kinetic) term ->
    (mode, m, a) env ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    m D.t ->
    (m, n, mn) D.plus ->
    (mode, kinetic) value =
 fun tm fldname fldty env tyargs m mn ->
  let values =
    match tm with
    | Ok tm -> `Ok (TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm))
    | Error e -> `Error e in
  (* MODALTODO: Allow nontrivial modalities for modal destructors *)
  let mode = mode_env env in
  let env =
    Value.Ext
      {
        env;
        plus = mn;
        filter = Modality.filter_id mode m;
        filtered = Modality.filter_id mode (D.plus_right mn);
        modality = Modality.id mode;
        values;
      } in
  (* This type is m-dimensional, hence must be instantiated at a full m-tube. *)
  let insttm = eval_term env fldty in
  let instargs =
    TubeOf.mmap
      {
        map =
          (fun fa [ arg ] ->
            let fains = ins_zero (dom_tface fa) in
            let tm = field_term arg.tm fldname fains in
            let ty = tyof_field (Ok arg.tm) arg.ty fldname ~shuf:Trivial fains in
            { tm; ty });
      }
      [ fst (TubeOf.split (D.zero_plus m) mn tyargs) ] in
  inst insttm instargs

(* This function is also called directly from check_higher_field.  In that case, the field is determined by a partial bijection that may *not* be just an insertion, and we have to frobnicate the environment in which we evaluate the type.  Some of that frobnication involves an eval-readback cycle, which requires a callback from here since readback isn't defined yet. *)
and tyof_higher_codatafield : type mode c n h s r i ic.
    ((mode, kinetic) value, Code.t) Result.t ->
    i Field.t ->
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
    (* The unevaluated type of the field is a term in context of this length i+[c;0].  The extra 0 is for the 'self' variable, which is always 0-dimensional when *defining* the codatatype. *)
    (mode, ic, kinetic) term ->
    (* In the nontrivial case, the return value is also in the degenerated context. *)
    (mode, kinetic) value =
 fun tm fldname codataenv tyargs fldins ~shuf ic0 fldty ->
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
  (* MODALTODO: Allow nontrivial modalities *)
  let mode = mode_env codataenv in
  let env =
    Value.Ext
      {
        env = codataenv;
        plus = D.plus_zero n;
        modality = Modality.id mode;
        filter = Modality.filter_id mode n;
        filtered = Modality.filter_zero (Modality.id mode);
        values;
      } in
  (* Now we act on this (n, [c;0]) env by the inverse of the insertion to get an (s+h, [c;0]) env. *)
  let env = Act (env, op_of_deg (deg_of_perm (perm_inv (perm_of_ins_plus fldins sh)))) in
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
        let env = Value.Act (env, op_of_deg (comp_deg swapdeg shuffledeg)) in
        (* Finally, now we can shift this to get a (s, i+[c;0]) env. *)
        Shift (env, si, ic0) in
  (* Now this matches the context of fldty, so we can evaluate it. *)
  let insttm = eval_term env fldty in
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
                let tm = field_term arg.tm fldname fains in
                let ty = tyof_field (Ok arg.tm) arg.ty fldname ~shuf fains in
                { tm; ty }
            | Nontrivial { dbwd = _; shuffle; deg_env = _; deg_nf } ->
                (* In this case, we have to degenerate the arguments, since they depend on the context. *)
                let arg = deg_nf arg in
                (* We also use these extra dimensions to make the pbij into an insertion. *)
                let (Plus rm) = D.plus (dom_tface faplus) in
                let arg_ins = ins_plus_of_pbij fains shuffle rm in
                let tm = field_term arg.tm fldname arg_ins in
                let ty = tyof_field (Ok arg.tm) arg.ty fldname ~shuf:Trivial arg_ins in
                { tm; ty });
      } in
  inst insttm instargs

(* This version is when we already know the insertion.  In this case, it's a bug if the field name or dimension don't match. *)
and tyof_field : type mode m h s r i c.
    ((mode, kinetic) value, Code.t) Result.t ->
    (mode, kinetic) value ->
    i Field.t ->
    (* We allow passing through a shuffle and eval-readback as well, in the case that this is a higher field being called recursively as part of the instantiation arguments. *)
    shuf:(mode, r, h, i, c) shuffleable ->
    (m, s, h) insertion ->
    (mode, kinetic) value =
 fun tm ty fld ~shuf fldins ->
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
      (type mn m n)
      (( head,
         Codata
           (type d a et)
           ({ env; fields; opacity = _; eta; termctx = _ } : (mode, m, n, d, a, et) codata_args),
         codatains,
         tyargs ) :
        mode head
        * (mode, m, n) canonical
        * (mn, m, n) insertion
        * (D.zero, mn, mn, mode normal) TubeOf.t) -> (
      (* The type cannot have a nonidentity degeneracy applied to it (though it can be at a higher dimension). *)
      match is_id_ins codatains with
      | None -> fatal ~severity (No_such_field (`Degenerated_record eta, errfld))
      | Some mn -> tyof_field_giventype tm head eta env mn fields tyargs fld ~shuf fldins)
  | Canonical (head, UU (mode, m), ins, tyargs) -> (
      let Eq = eq_of_ins_zero ins in
      let err = Code.No_such_field (`Type errtm, errfld) in
      match Fibrancy.FieldsMap.find_opt mode !Fibrancy.fields with
      | None -> fatal ~severity err
      | Some fields ->
          let values =
            match tm with
            | Ok tm -> `Ok (TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm))
            | Error e -> `Error e in
          let env =
            Value.Ext
              {
                env = Value.Emp (mode, m);
                plus = D.plus_zero m;
                modality = Modality.id mode;
                filter = Modality.filter_id mode m;
                filtered = Modality.filter_zero (Modality.id mode);
                values;
              } in
          tyof_field_giventype tm head Noeta env (D.plus_zero m) fields tyargs fld ~shuf fldins)
  | _ ->
      let p =
        match tm with
        | Ok tm -> Dump.Val tm
        | Error _err -> PString "[ERROR]" in
      fatal ~severity (No_such_field (`Other p, errfld))

and tyof_field_giventype : type mode m n mn h s r i c et a k.
    ((mode, kinetic) value, Code.t) Result.t ->
    mode head ->
    (potential, et) eta ->
    (mode, m, a) env ->
    (m, n, mn) D.plus ->
    (mode * a * n * et) Term.CodatafieldAbwd.t ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    i Field.t ->
    shuf:(mode, r, h, i, c) shuffleable ->
    (k, s, h) insertion ->
    (mode, kinetic) value =
 fun tm head eta env mn fields tyargs fld ~shuf fldins ->
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
          let shuf : (mode, r, h, i, a) shuffleable =
            match shuf with
            | Trivial -> Trivial
            | Nontrivial { dbwd; _ } -> (
                match Tctx.compare dbwd (length_env env) with
                | Eq -> shuf
                | Neq -> fatal (Anomaly "context length mismatch in tyof_field")) in
          tyof_codatafield tm fld fldty env tyargs m mn ~shuf fldins
      | Not_found -> fatal ~severity (No_such_field (`Record (eta, phead head), errfld))
      | Wrong_dimension (i, _) ->
          let errsuffix =
            match shuf with
            | Trivial -> `Ins fldins
            | Nontrivial { shuffle; _ } -> `Pbij (Pbij (fldins, shuffle)) in
          fatal ~severity (Wrong_dimension_of_field (eta, phead head, `Field fld, m, i, errsuffix)))

(* This version is for when we are synthesizing the insertion, so we return the resulting insertion along with the type.  The field might also be given positionally in this case, so we also return the field name when we find it.  In this case, mismatches in field names or dimensions are user errors. *)
and tyof_field_withname : type mode a b.
    (mode, a, b) Ctx.t ->
    ((mode, kinetic) value, Code.t) Result.t ->
    (mode, kinetic) value ->
    [ `Name of string * int list | `Int of int ] ->
    Field.with_ins * (mode, kinetic) value =
 fun ctx tm ty infld ->
  let errfld =
    match infld with
    | `Name (str, ints) -> `Strings (str, ints)
    | `Int n -> `Int n in
  let errtm =
    match tm with
    | Ok tm -> PVal (ctx, tm)
    | Error _err -> PString "[ERROR]" in
  match view_type ~severity:Asai.Diagnostic.Error ty "tyof_field" with
  | Canonical (head, Codata { env; fields; opacity = _; eta; termctx = _ }, codatains, tyargs) -> (
      (* The type cannot have a nonidentity degeneracy applied to it (though it can be at a higher dimension). *)
      match is_id_ins codatains with
      | None -> fatal (No_such_field (`Degenerated_record eta, errfld))
      | Some mn ->
          let err = Code.No_such_field (`Record (eta, phead head), errfld) in
          tyof_field_withname_giventype ctx tm ty eta env mn fields tyargs infld err)
  | Canonical (_head, UU (mode, m), ins, tyargs) -> (
      let Eq = eq_of_ins_zero ins in
      let err = Code.No_such_field (`Type errtm, errfld) in
      match Fibrancy.FieldsMap.find_opt mode !Fibrancy.fields with
      | None -> fatal err
      | Some fields ->
          let values =
            match tm with
            | Ok tm -> `Ok (TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm))
            | Error e -> `Error e in
          let env =
            Value.Ext
              {
                env = Value.Emp (mode, m);
                plus = D.plus_zero m;
                modality = Modality.id mode;
                filter = Modality.filter_id mode m;
                filtered = Modality.filter_zero (Modality.id mode);
                values;
              } in
          tyof_field_withname_giventype ctx tm ty Noeta env (D.plus_zero m) fields tyargs infld err)
  | _ -> fatal (No_such_field (`Other errtm, errfld))

(* Subroutine of tyof_field_withname for after we've identified the type of the head as either a codatatype or a universe (for fibrancy fields). *)
and tyof_field_withname_giventype : type mode a b m n mn c et.
    (mode, a, b) Ctx.t ->
    ((mode, kinetic) value, Code.t) Result.t ->
    (mode, kinetic) value ->
    (potential, et) eta ->
    (mode, m, c) env ->
    (m, n, mn) D.plus ->
    (mode * c * n * et) Term.CodatafieldAbwd.t ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    [ `Name of string * int list | `Int of int ] ->
    Code.t ->
    Field.with_ins * (mode, kinetic) value =
 fun ctx tm ty eta env mn fields tyargs infld err ->
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
              let fldty = tyof_codatafield tm fld fldty env tyargs m mn ~shuf:Trivial fldins in
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
                      let fldty =
                        tyof_codatafield tm fld fldty env tyargs m mn ~shuf:Trivial fldins in
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
            let fldty = tyof_codatafield tm fld fldty env tyargs m mn ~shuf:Trivial fldins in
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
            modality;
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
                           (defer (fun () -> Val (CubeOf.find argstbl fa)))
                           (deg_of_perm fb) None);
                   });
          })
       body)
    (deg_of_perm perm) None

and eval_canonical : type mode m a.
    (mode, m, a) env -> (mode, a) Term.canonical -> (mode, potential) evaluation =
 fun env can ->
  match can with
  | Data { indices; constrs; discrete } ->
      let tyfam = ref None in
      let constrs =
        Abwd.map
          (fun (Term.Dataconstr { args; indices }) -> Value.Dataconstr { env; args; indices })
          constrs in
      let dim, mode = (dim_env env, mode_env env) in
      let canonical = Data { dim; tyfam; indices = Fillvec.empty indices; constrs; discrete } in
      let tyargs = TubeOf.empty (dim_env env) in
      let fields =
        match Lazy.force Fibrancy.data with
        | None -> Bwd.Emp
        | Some () -> fatal (Unimplemented "fibrancy of datatypes") in
      Val
        (Canonical
           { mode; canonical; tyargs; ins = ins_zero dim; fields; inst_fields = Some fields })
  | Codata c ->
      eval_codata env c.eta c.opacity c.dim (Lazy.from_val c.termctx) c.fields
        (Fibrancy.Codata.finished (mode_env env) c)

(* We split out this subroutine so it can be called from Check.with_codata_so_far and a lazy termctx.  *)
and eval_codata : type mode m a c n et.
    (mode, m, a) env ->
    (potential, et) eta ->
    opacity ->
    n D.t ->
    (mode, c, (a, (mode id, n) dim_entry) snoc) termctx option Lazy.t ->
    (mode * a * n * et) CodatafieldAbwd.t ->
    (mode * (n * a * potential * no_eta)) Term.StructfieldAbwd.t ->
    (mode, potential) evaluation =
 fun env eta opacity n termctx fields fibrancy_fields ->
  let m = dim_env env in
  let (Plus (type mn) (m_n : (m, n, mn) D.plus)) = D.plus n in
  let mn = D.plus_out m m_n in
  let ins = id_ins m m_n in
  let canonical = Codata { eta; opacity; env; termctx; fields } in
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
      let lenv = key_env env filt_p_q (Modalcell.id modality) al in
      (* We make everything lazy, since we can, and not everything may end up being used. *)
      Value.Ext
        {
          env = evalled_env;
          plus = pm_k;
          modality;
          filter = filt_pm_qn;
          filtered = filt_k_k;
          values =
            `Lazy
              (CubeOf.build pmk
                 {
                   build =
                     (fun fab ->
                       let (SFace_of_plus (_, fa, fb)) = sface_of_plus p_mk fab in
                       lazy_eval (act_env lenv (op_of_sface fa)) (CubeOf.find xss fb));
                 });
        }
  | Key
      (type mu nu cod a m b)
      ({ env = tmenv; filter = filt_term; cell; plus_src; plus_tgt } :
        (_, mu, nu, cod, _, a, m, b, _, _) key_args) ->
      (* We strip the keys corresponding to the codomain of the cell off of the ambient environment, evaluate the term environment in the bare environment underneath them, and re-apply a single composite key.  The composite key filters the dimension by the vertical source of the cell, which can be more filtered than the dimension of the ambient environment (which is filtered by the vertical target); so we apply a degeneracy outside, along with the operators stripped off of the ambient environment, to produce the correct dimension. *)
      let (Stripped (senv, f_nu_p, sop, keys)) = Env.strip_keys env plus_tgt in
      let p = dim_env senv in
      let mm = dim_term_env tmenv in
      let (Plus p_m) = D.plus mm in
      let evalled = eval_env senv p_m tmenv in
      let pm = D.plus_out p p_m in
      let (Has_filter f_mu_pm) = Modality.filter (Modalcell.vsrc cell) pm in
      let (Filter_of_plus (mup_muk, f_mu_p, f_mu_m)) = Modality.filter_of_plus p_m f_mu_pm in
      let Eq = Modality.filter_uniq f_mu_m filt_term in
      let keyed = key_env evalled f_mu_pm (Modalcell.vcomp keys cell) plus_src in
      let d = Modalcell.filter_deg cell p f_mu_p f_nu_p in
      act_env keyed (op_plus (comp_op (op_of_deg d) sop) mup_muk q_n)

and apply_term : type dom modality mode n.
    (mode, kinetic) value ->
    (dom, modality, mode) Modality.t ->
    (n, (dom, kinetic) value) CubeOf.t ->
    (mode, kinetic) value =
 fun fn modality arg ->
  let (Val v) = apply fn modality arg in
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
and app_eval_apps : type mode s any.
    (mode, s) evaluation -> (mode, any) apps -> (mode, s) evaluation =
 fun ev x ->
  match x with
  | Emp -> ev
  | Arg (rest, modality, xs, ins) -> (
      let (To p) = deg_of_ins ins in
      match app_eval_apps ev rest with
      | Val tm -> act_evaluation (apply tm modality (val_of_norm_cube xs)) p None
      | Realize tm ->
          let (Val v) = act_evaluation (apply tm modality (val_of_norm_cube xs)) p None in
          Realize v
      | Unrealized -> Unrealized)
  | Field (rest, fld, fldplus, ins) -> (
      let (To p) = deg_of_ins ins in
      match app_eval_apps ev rest with
      | Val tm -> act_evaluation (field tm fld (id_ins (cod_left_ins ins) fldplus)) p None
      | Realize tm ->
          let (Val v) = act_evaluation (field tm fld (id_ins (cod_left_ins ins) fldplus)) p None in
          Realize v
      | Unrealized -> Unrealized)
  | Inst (rest, _, args) -> (
      match app_eval_apps ev rest with
      | Val tm -> Val (inst tm args)
      | Realize tm -> Realize (inst tm args)
      | Unrealized -> Unrealized)

(* Look up a cube of values in an environment by variable index.  The variable index points into the prefix of a decomposition of the codomain of the environment whose remaining part consists of the locks annotating the variable; the keys whose sources make up those locks are consumed as we pass them, accumulating their horizontal composite into 'acc.

   Crucially, this recursion proceeds *bottom-up* (just like replace_keys_rec): the navigation down to the entry is driven by the index 'v and the decomposition, but the operator that selects and acts on the looked-up cube is assembled on the *return* path.  This means every operator and shift is pushed *along* a filter in the degeneracy direction (with filter_op, filter_comp, deg_of_filter), never in the section direction, so we never have to choose an endpoint to fill in a filtered-away direction.  It therefore works even in a theory with no endpoints.

   As in replace_keys_rec, we thread 'acc (the horizontal composite of the keys consumed so far, whose vertical source 'sigma is the composite of the consumed locks) and 'sigma_comp (witnessing that the remaining locks composed with 'sigma equal the variable's total modality 'mu).  The returned filter, at each level, is by 'sigma; at the top, 'sigma is the identity (no keys consumed yet) so the filter is the identity.  The intrinsic dimension 'k of the cube variable is carried along untouched (in 'filtered and 'plus) and recombined with the variable's own face only at the end, in lookup. *)
and lookup_cube : type dom mu sigma tau cod murest mcur n a bn b k.
    (mcur, n, b) env ->
    (bn, cod, murest, mcur, b) plus_with_locks ->
    (dom, sigma, mcur, murest, cod, mu) Modality.comp ->
    (dom, sigma, tau, mcur) Modalcell.t ->
    (dom, mu, cod) Modality.t ->
    (a, mu, k, bn) insert ->
    (dom, sigma, mcur, cod, mu, k, n) looked_up_cube =
 fun env (Plus_with_locks (bc, llc)) sigma_comp acc mu v ->
  match (bc, llc, env) with
  (* When we encounter a key, we accumulate it horizontally onto acc (exactly as in replace_keys_rec), recurse, and on the way back recompute the filter at this (more-filtered) level, confirming with the key that it composes to the deeper filter.  The operator passes through unchanged: crossing a key does not change the filtered dimension at which the operator acts. *)
  | b_cn, llcn, Key (env1, filt1, key1, Plus_lock (ln, bc_n)) -> (
      let lln = locks_lock ln in
      let cn, nn = (Locks.dom llcn, Lock.cod ln) in
      match Tctx.factor cn nn with
      | None -> fatal (Anomaly "lookup_cube: key sources cross the decomposition")
      | Some (Factor (_c, c_n)) ->
          let (Uncomp (llc, lln', m_n)) = Locks.uncomp c_n llcn in
          let Eq = Locks.uniq lln lln' in
          let b_c = Tctx.comp_assoc_cancelr c_n b_cn bc_n in
          let sigma = Modalcell.vsrc acc in
          let (Comp s_mu1) = Modality.comp sigma in
          let sigma1_comp = Modality.comp_assocr m_n s_mu1 sigma_comp in
          let (Comp nus) = Modality.comp (Modalcell.vtgt acc) in
          let acc' = Modalcell.hcomp s_mu1 nus key1 acc in
          let (Looked_up { act; op; filter = f1; filtered; plus; entry; cell }) =
            lookup_cube env1 (Plus_with_locks (b_c, llc)) sigma1_comp acc' mu v in
          let (Has_filter f_sig) = Modality.filter sigma (dim_env env) in
          let f_comb = Modality.filter_comp s_mu1 filt1 f_sig in
          let Eq = Modality.filter_uniq f_comb f1 in
          Looked_up { act; op; filter = f_sig; filtered; plus; entry; cell })
  (* A dimension entry in the lock region of the decomposition can't be our variable, so we skip it. *)
  | Suc (b_cn, Dim _), Suc (llcn, Locks_dim _, Zero), Ext { env = env1; _ } ->
      lookup_cube env1 (Plus_with_locks (b_cn, llcn)) sigma_comp acc mu v
  | Suc (b_cn, Dim _), Suc (llcn, Locks_dim _, Zero), Locked_ext { env = env1; _ } ->
      lookup_cube env1 (Plus_with_locks (b_cn, llcn)) sigma_comp acc mu v
  (* An operator action is pushed onto the (returned) operator by filtering it by the deeper filter, exactly the degeneracy-direction move that replace_keys_rec uses to push an action outside a key. *)
  | _, _, Act (env1, op') ->
      let (Looked_up { act; op; filter = f1; filtered; plus; entry; cell }) =
        lookup_cube env1 (Plus_with_locks (bc, llc)) sigma_comp acc mu v in
      let (Filter_op (op'f, f')) = Modality.filter_op f1 op' in
      Looked_up { act; op = comp_op op op'f; filter = f'; filtered; plus; entry; cell }
  (* If the environment is permuted, we transfer the decomposition and the index across the permutation; the permutation only touches dimension entries, not the dimension, so the looked-up cube passes through unchanged. *)
  | _, _, Permute (perm, env1) -> (
      match unpermute_plus_locks perm bc llc with
      | None -> fatal (Anomaly "lookup_cube: permutation crosses the decomposition")
      | Some (Unpermute (perm2, bd, lld)) ->
          let (Permute_insert (v, _)) = permute_insert v perm2 in
          lookup_cube env1 (Plus_with_locks (bd, lld)) sigma_comp acc mu v)
  (* TODO: A shift or unshift moves dimensions between the substitution dimension and the codomain, i.e. between the environment dimension and the looked-up variable's *intrinsic* dimension 'k.  Handling them endpoint-free therefore requires letting 'k vary as we return up through the recursion (the migrating dimensions are filtered, in the degeneracy direction, not selected with an endpoint-choosing face).  That needs an extension of the "env-dimension-only, 'k fixed" separation this recursion currently relies on, so it is left as an anomaly for now.  Note that it is already endpoint-free: neither case calls sface_of_filter. *)
  (* TODO: A shift is dual to the unshift below: it moves dimensions from the substitution dimension into the codomain, so going back up the looked-up variable's intrinsic dimension k *grows* (from x to z = q + x, via uncoinsert), with the migrated q directions being degenerate for the looked-up value (they come from the environment, not from the stored cube).  The environment/operator bookkeeping is the dual of the unshift case (split the returned sigma-filter with filter_of_plus, push a collapse through it with filter_deg), but realizing the k-growth requires the stored entry cube to be *extended by degenerate directions* (or the final degeneracy applied in lookup to carry them), which the env-dimension-only / cube-valued representation here doesn't yet express.  Still endpoint-free: no sface_of_filter. *)
  | _, _, Shift _ -> fatal (Anomaly "lookup_cube: shift not yet reimplemented endpoint-free")
  (* An unshift pulls dimensions out of the codomain into the substitution dimension.  For the looked-up variable, those dimensions were part of its intrinsic dimension in the inner environment, so the recursion runs at a larger intrinsic dimension px = q + vx; on the return path we migrate the q part back into the environment dimension by re-associating the entry's mfilt+px split.  The shift dimension is decomposed in the order dictated by sigma_comp (mu = murest o sigma; NO filter commutativity assumed): collapse it by the not-yet-consumed keys murest, then filter that by sigma.  Pushing the murest-collapse through the sigma-filter with filter_deg yields, consistently, the environment-side sigma-filter g (keeping the residual that murest will eventually remove) and the degeneracy d_sn collapsing it to the migrated part q (in which the looked-up value is constant).  All in the degeneracy direction, so endpoint-free. *)
  | b_cn, llcn, Unshift (env1, n_x, xb) ->
      let sx = D.plus_right n_x in
      let (Uncomp (nbm, ncm, nb_nc)) = Plusmap.uncomp sx b_cn xb in
      let (Eq _) = Plusmap.tgt ncm in
      let ll_nc = Plusmap.locks sx ncm llcn in
      let (Uninsert (q_vx, f_q, v, _)) = Plusmap.uninsert v nbm in
      (* uninsert binds f_q's source/target modes existentially; recover that they are mu's. *)
      let Eq, Eq = Modality.filter_dim_modes f_q mu in
      let (Looked_up { act; op; filter = f1; filtered; plus; entry; cell }) =
        lookup_cube env1 (Plus_with_locks (nb_nc, ll_nc)) sigma_comp acc mu v in
      (* Decompose the shift dimension as murest then sigma (the order of sigma_comp; no commutativity), and push the murest-collapse through the sigma-filter to get the environment filter g and the collapsing degeneracy d_sn together; q is the migrated (mu-filtered) part. *)
      let murest = Modality.comp_left sigma_comp mu in
      let (Has_filter h) = Modality.filter murest sx in
      let deg_collapse = Modality.deg_of_filter sx h in
      let (Has_filter g_b) = Modality.filter (Modalcell.vsrc acc) (Modality.filtered sx h) in
      let (Filter_deg (d_sn, g)) = Modality.filter_deg g_b deg_collapse in
      let Eq = Modality.filter_uniq (Modality.filter_comp sigma_comp h g_b) f_q in
      let q = Modality.filtered (Modality.filtered sx h) g_b in
      (* Re-split the recursion's intrinsic dimension px = q + vx.  Since px is mu-invariant (filtered is the identity on px), so is the leftover vx: the q-part of the split is the identity (filter_idempotent of f_q), and right-cancellation then forces the vx-part to be (vx, vx). *)
      let (Filter_of_plus (plus_avc, f_a, filtered_vx)) = Modality.filter_of_plus q_vx filtered in
      let Eq = Modality.filter_uniq f_a (Modality.filter_idempotent f_q) in
      let Eq = D.minus_uniq' q plus_avc q_vx in
      let (Plus mfilt_q) = D.plus q in
      let plus_node = D.plus_assocl mfilt_q q_vx plus in
      let sn = Modality.filtered sx g in
      let (Plus m_in_sn) = D.plus sn in
      let f_node = Modality.filter_plus m_in_sn n_x f1 g in
      let op_node = op_plus_op op mfilt_q m_in_sn (op_of_deg d_sn) in
      Looked_up
        {
          act;
          op = op_node;
          filter = f_node;
          filtered = filtered_vx;
          plus = plus_node;
          entry;
          cell;
        }
  (* Below all the locks, if we encounter a variable that isn't ours, we skip it and proceed.  When we find our variable, the consumed locks are exactly the variable's annotation: sigma = mu, so acc is the composite of the keys and the entry's filter is by mu.  We start the operator at the identity on the filtered dimension; it gets composed with the variable's own face in lookup.  The forcing function is the identity if the entry is not lazy, and force_eval_term if it is lazy. *)
  | ( (Zero as bc0),
      (Zero _ as llc0),
      Ext { env = env1; plus = mk; modality; filter; filtered; values } ) -> (
      match v with
      | Later v -> lookup_cube env1 (Plus_with_locks (bc0, llc0)) sigma_comp acc mu v
      | Now -> (
          let Eq = Modality.comp_uniq sigma_comp (Modality.id_comp (Modalcell.vsrc acc)) in
          match (values, Modality.compare modality mu) with
          (* Looking up a variable that's bound to an error immediately fails with that error.  (In particular, this sort of failure can't currently happen "deeper" inside a term.) *)
          | `Error e, _ -> fatal e
          | `Ok entry, Eq ->
              let mfilt = Modality.filtered (dim_env env1) filter in
              Looked_up
                {
                  act = (fun x s c -> act_value x s c);
                  op = id_op mfilt;
                  filter;
                  filtered;
                  plus = mk;
                  entry;
                  cell = Wrap acc;
                }
          | `Lazy entry, Eq ->
              let mfilt = Modality.filtered (dim_env env1) filter in
              Looked_up
                {
                  act = (fun x s c -> force_eval_term (act_lazy_eval x s c));
                  op = id_op mfilt;
                  filter;
                  filtered;
                  plus = mk;
                  entry;
                  cell = Wrap acc;
                }
          | `Ok _, Neq | `Lazy _, Neq ->
              fatal (Modality_mismatch (`Internal, "lookup_cube keys", modality, mu))))
  (* A locked-out entry carries no data: if it's not our variable we skip it, but looking it up directly is an anomaly (its values were discarded when the environment was rebuilt behind a nonparametric key). *)
  | (Zero as bc0), (Zero _ as llc0), Locked_ext { env = env1; _ } -> (
      match v with
      | Later v -> lookup_cube env1 (Plus_with_locks (bc0, llc0)) sigma_comp acc mu v
      | Now -> fatal (Anomaly "lookup of locked-out (permanently inaccessible) variable"))
  (* Since there's an index into the prefix, the environment can't be empty when the decomposition runs out. *)
  | Zero, Zero _, Emp _ -> (
      match v with
      | _ -> .)
  (* Nothing else is possible, since if the tctx has a nonzero lock on it, the environment can't be empty or end with a value entry. *)
  | Suc (_, Lock _), Suc (_, Locks_lock _, Suc (_, _)), _ -> .
  | Suc (_, Proj _), Suc (_, _, _), _ -> .

and lookup : type mode m bkm. (mode, m, bkm) env -> (mode, bkm) index -> (mode, kinetic) value =
 fun env
     (Index
        (type b l k bn mu cod)
        ((v, fa, filter_mu_k_k, plus) :
          (b, mu, k, bn) insert
          * (l, k) sface
          * (mode, mu, cod, k, k) Modality.filter_dim
          * (bn, cod, mu, mode, bkm) plus_lock)) ->
  let m = dim_env env in
  let k = cod_sface fa in
  let l = dom_sface fa in
  let mu = plus_lock_modality plus in
  ignore (k, m);
  match
    lookup_cube env
      (plus_with_locks_of_plus_lock plus)
      (Modality.comp_id mu)
      (Modalcell.id2 (mode_env env))
      mu v
  with
  | Looked_up { act; op; filter; filtered; plus = mfk; entry; cell = Wrap keys } ->
      (* At the top no keys have been consumed, so the returned filter is the identity; the operator already acts at the variable's filtered dimension (the values in the inaccessible directions behind the locks have simply not been touched).  We recombine the variable's intrinsic dimension by composing with its own face, and confirm that the entry's intrinsic part matches the variable's annotation. *)
      let Eq = Modality.eq_of_filter_id filter in
      let Eq = Modality.filter_uniq filtered filter_mu_k_k in
      let (Plus m_l) = D.plus l in
      let (Op (f, s)) = op_plus_op op mfk m_l (op_of_sface fa) in
      act (CubeOf.find entry f) s (Some keys)

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
              let value = inst_lazy value args2 in
              (* Now we have to construct the type OF the new instantiation.  The old term must have belonged to some instantiation of the universe of the previously uninstantiated dimension. *)
              match view_type ty "inst" with
              | Canonical (_, UU (mode, m), ins, tys1) -> (
                  let Eq = eq_of_ins_zero ins in
                  match D.compare m (TubeOf.uninst args1) with
                  | Neq ->
                      fatal (Dimension_mismatch ("instantiating a type 2", m, TubeOf.uninst args1))
                  | Eq ->
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
              let inst_fields = inst_fibrancy_fields mode fields args in
              Canonical { mode; canonical = c; tyargs = args; ins; fields; inst_fields })
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
                struct_field ~unset_ok:true "fibrancy" Potential fields Fibrancy.fid fldins in
              let (Snoc (Snoc (Emp, xcube), ycube)) = TubeOf.to_cube_bwv one l outer in
              let idm = Modality.id mode in
              let v =
                match
                  app_eval_apps idfld
                    (Arg
                       ( Arg (Emp, idm, xcube, ins_zero (CubeOf.dim xcube)),
                         idm,
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
  let module MC = CubeOf.Monadic (Monad.State (struct
    type t = (mode, kinetic) value
  end))
  in
  snd
    (MC.miterM
       { it = (fun _ [ x ] fn -> ((), apply_term fn modality (CubeOf.singleton x))) }
       [ xs ] fn)

let apply_singleton_nfs : type dom modality mode n.
    (dom, modality, mode) Modality.t ->
    (mode, kinetic) value ->
    (n, dom normal) CubeOf.t ->
    (mode, kinetic) value =
 fun modality fn xs ->
  let module MC = CubeOf.Monadic (Monad.State (struct
    type t = (mode, kinetic) value
  end))
  in
  snd
    (MC.miterM
       { it = (fun _ [ x ] fn -> ((), apply_term fn modality (CubeOf.singleton x.tm))) }
       [ xs ] fn)

let apply_singleton_tube_nfs : type dom modality mode n.
    (dom, modality, mode) Modality.t ->
    (mode, kinetic) value ->
    (D.zero, n, n, dom normal) TubeOf.t ->
    (mode, kinetic) value =
 fun modality fn xs ->
  let module MC = TubeOf.Monadic (Monad.State (struct
    type t = (mode, kinetic) value
  end))
  in
  snd
    (MC.miterM
       { it = (fun _ [ x ] fn -> ((), apply_term fn modality (CubeOf.singleton x.tm))) }
       [ xs ] fn)

(* Evaluate a term context to produce a value context. *)

let eval_bindings : type dom modality mode a b n bm.
    (mode, a, b) Ctx.Ordered.t ->
    (* These two arguments are redundant *)
    (dom, modality, mode) Modality.t ->
    (dom, modality, mode, n, n) Modality.filter_dim ->
    ((b, (modality, n) dim_entry) snoc, mode, modality, dom, bm) plus_lock ->
    (n, (dom, bm) binding) CubeOf.t ->
    (n, dom Ctx.Binding.t) CubeOf.t =
 fun ctx modality filter al cbs ->
  let i = Ctx.Ordered.length ctx in
  let vbs = CubeOf.build (CubeOf.dim cbs) { build = (fun _ -> Ctx.Binding.unknown ()) } in
  let ctx = Ctx.Ordered.invis ctx modality filter vbs in
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
      let modality = plus_lock_modality plus_lock in
      let bindings = eval_bindings ctx modality filter plus_lock bindings in
      let fields = Bwv.map (fun (f, x, _) -> (f, x)) fields in
      Vis { dim; modality; filter; plusdim; vars; bindings; hasfields; fields; fplus }
  | Invis { plus_lock; bindings; filter } ->
      let modality = plus_lock_modality plus_lock in
      Invis { modality; filter; bindings = eval_bindings ctx modality filter plus_lock bindings }

let rec eval_ordered_ctx : type mode a b. (mode, a, b) ordered_termctx -> (mode, a, b) Ctx.Ordered.t
    = function
  | Emp mode -> Emp mode
  | Ext (ctx, e, af) ->
      let ectx = eval_ordered_ctx ctx in
      Snoc (ectx, eval_entry ectx e, af)
  | Lock (ctx, lock) -> Lock (eval_ordered_ctx ctx, lock)
  | Parametric_lock ctx -> Parametric_lock (eval_ordered_ctx ctx)

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
