open Bwd
open Util
open Tbwd
open Reporter
open Dim
open Syntax
open Term
open Value
open Act
open Printable

(* Since some entries in an environment are lazy and some aren't, lookup_cube returns a cube whose entries belong to an existential type, along with a function to force any element of that type into a value. *)
type (_, _) looked_up_cube =
  | Looked_up :
      ('a -> kinetic value) * ('m, 'n) op * ('k, ('n, 'a) CubeOf.t) CubeOf.t
      -> ('m, 'k) looked_up_cube

(* A full tube of objects. *)
type _ full_tube = Full_tube : (D.zero, 'n, 'n, 'a) TubeOf.t -> 'a full_tube

(* Require that the supplied list contains exactly b (which is a Fwn) arguments, rearrange each mn-cube argument into an n-cube of m-cubes, and add all of them to the given environment. *)
let rec take_args :
    type m n mn a b ab.
    (m, a) env ->
    (m, n, mn) D.plus ->
    (mn, kinetic value) CubeOf.t list ->
    (a, b, n, ab) Tbwd.snocs ->
    (m, ab) env =
 fun env mn dargs plus ->
  let m = dim_env env in
  let n = D.plus_right mn in
  match (dargs, plus) with
  | [], Zero -> env
  | arg :: args, Suc plus ->
      let env =
        Ext
          ( env,
            CubeOf.build n
              {
                build =
                  (fun fb ->
                    CubeOf.build m
                      {
                        build =
                          (fun fa ->
                            let (Plus jk) = D.plus (dom_sface fb) in
                            let fab = sface_plus_sface fa mn jk fb in
                            CubeOf.find arg fab);
                      });
              } ) in
      take_args env mn args plus
  | _ -> fatal (Anomaly "wrong number of arguments in argument list")

(* A "view" is the aspect of a type or term that we match against to determine its behavior.  A view of a term is just another term, but in WHNF.  A view of a type is either a universe, a pi-type, another canonical type (data or codata), or a neutral.  The non-neutral sorts come with their instantiations that have been checked to have the correct dimension. *)

type view_type =
  | UU : (D.zero, 'k, 'k, normal) TubeOf.t -> view_type
  | Pi :
      string option
      * ('k, kinetic value) CubeOf.t
      * ('k, unit) BindCube.t
      * (D.zero, 'k, 'k, normal) TubeOf.t
      -> view_type
  | Canonical : head * 'k canonical * (D.zero, 'k, 'k, normal) TubeOf.t -> view_type
  | Neutral : view_type

let rec view_term : type s. s value -> s value =
 fun tm ->
  if GluedEval.read () then
    match tm with
    | Uninst (Neu { value; _ }, ty) -> (
        (* For glued evaluation, when viewing a term, we force its value and proceed to view that value instead. *)
        match force_eval value with
        | Realize v -> view_term v
        | Canonical (Data d) when Option.is_none !(d.tyfam) ->
            d.tyfam := Some (lazy { tm; ty = Lazy.force ty });
            tm
        | _ -> tm)
    | _ -> tm
  else tm

(* Viewing a type fails if the argument is not fully instantiated.  In most situations this would be a bug, but we allow the caller to specify it differently, since during typechecking it could be a user error. *)
and view_type ?severity (ty : kinetic value) (err : string) : view_type =
  let uty, Full_tube tyargs =
    match ty with
    (* Since we expect fully instantiated types, in the uninstantiated case the dimension must be zero. *)
    | Uninst (ty, (lazy (Uninst (UU n, _)))) -> (
        match D.compare n D.zero with
        | Eq -> (ty, Full_tube (TubeOf.empty D.zero))
        | Neq -> fatal ?severity (Type_not_fully_instantiated (err, n)))
    | Uninst _ -> fatal ?severity (Type_expected err)
    | Inst { tm = ty; dim = _; args; tys = _ } -> (
        match D.compare (TubeOf.uninst args) D.zero with
        | Eq ->
            let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus (TubeOf.inst args)) in
            (ty, Full_tube args)
        | Neq -> fatal ?severity (Type_not_fully_instantiated (err, TubeOf.uninst args)))
    | _ -> fatal ?severity (Anomaly ("expected type in " ^ err)) in
  match uty with
  | UU n -> (
      match (D.compare n (TubeOf.inst tyargs), D.compare (TubeOf.uninst tyargs) D.zero) with
      | Eq, Eq ->
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (TubeOf.inst tyargs)) in
          UU tyargs
      | _, Neq -> fatal ?severity (Type_not_fully_instantiated (err, TubeOf.uninst tyargs))
      | Neq, _ -> fatal (Dimension_mismatch ("view universe", n, TubeOf.inst tyargs)))
  | Pi (x, doms, cods) -> (
      match
        (D.compare (CubeOf.dim doms) (TubeOf.inst tyargs), D.compare (TubeOf.uninst tyargs) D.zero)
      with
      | Eq, Eq ->
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (TubeOf.inst tyargs)) in
          Pi (x, doms, cods, tyargs)
      | _, Neq -> fatal ?severity (Type_not_fully_instantiated (err, TubeOf.inst tyargs))
      | Neq, _ -> fatal (Dimension_mismatch ("view pi-type", CubeOf.dim doms, TubeOf.inst tyargs)))
  | Neu { head; args = _; value } -> (
      (* Glued evaluation: when viewing a type, we force its value and proceed to view that value instead. *)
      match force_eval value with
      | Canonical c -> (
          (match c with
          | Data d when Option.is_none !(d.tyfam) ->
              d.tyfam := Some (lazy { tm = ty; ty = inst (universe (TubeOf.inst tyargs)) tyargs })
          | _ -> ());
          match
            ( D.compare (dim_canonical c) (TubeOf.inst tyargs),
              D.compare (TubeOf.uninst tyargs) D.zero )
          with
          | Eq, Eq ->
              let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (TubeOf.inst tyargs)) in
              Canonical (head, c, tyargs)
          | _, Neq -> fatal ?severity (Type_not_fully_instantiated (err, TubeOf.uninst tyargs))
          | Neq, _ ->
              fatal (Dimension_mismatch ("view canonical", dim_canonical c, TubeOf.inst tyargs)))
      | Realize v -> view_type ?severity (inst v tyargs) err
      | _ -> Neutral)

(* Evaluation of terms and evaluation of case trees are technically separate things.  In particular, evaluating a kinetic (standard) term always produces just a value, whereas evaluating a potential term (a function case tree) can either

   1. Produce a new partially-evaluated case tree that isn't fully applied yet.  This is actually represented by a value that's either a Lam or a Struct.
   2. Reach a leaf and produce a value.
   3. Conclude that the case tree is true neutral and will never reduce further.

   These possibilities are encoded in an "evaluation", defined in Syntax.Value.  The point is that, just as with the representation of terms, there is enough commonality between the two (application of lambdas and field projection from structs) that we don't want to duplicate the code, so we define the evaluation functions to return an "evaluation" result that is a GADT parametrized by the kind of energy of the term. *)

(* The master evaluation function. *)
and eval : type m b s. (m, b) env -> (b, s) term -> s evaluation =
 fun env tm ->
  match tm with
  | Var v -> Val (lookup env v)
  | Const name -> (
      let dim = dim_env env in
      let cty, defn = Global.find name in
      (* Its type must also be instantiated at the lower-dimensional versions of itself. *)
      let ty =
        lazy
          (inst (eval_term (Emp dim) cty)
             (TubeOf.build D.zero (D.zero_plus dim)
                {
                  build =
                    (fun fa ->
                      (* To compute those lower-dimensional versions, we recursively evaluate the same constant in lower-dimensional contexts. *)
                      let tm =
                        eval_term (act_env env (op_of_sface (sface_of_tface fa))) (Const name) in
                      (* We need to know the type of each lower-dimensional version in order to annotate it as a "normal" instantiation argument.  But we already computed that type while evaluating the term itself, since as a normal term it had to be annotated with its type. *)
                      match tm with
                      | Uninst (Neu _, (lazy ty)) -> { tm; ty }
                      | _ -> fatal (Anomaly "eval of lower-dim constant not neutral/canonical"));
                })) in
      let head = Const { name; ins = ins_zero dim } in
      match defn with
      | Defined tree -> (
          if GluedEval.read () then
            (* Glued evaluation: we evaluate the definition lazily and return a neutral with that lazy evaluation stored. *)
            Val (Uninst (Neu { head; args = Emp; value = lazy_eval (Emp dim) tree }, ty))
          else
            match eval (Emp dim) tree with
            | Realize x -> Val x
            | Canonical (Data d) as value ->
                let newtm = Uninst (Neu { head; args = Emp; value = ready value }, ty) in
                if Option.is_none !(d.tyfam) then
                  d.tyfam := Some (lazy { tm = newtm; ty = Lazy.force ty });
                Val newtm
            | value -> Val (Uninst (Neu { head; args = Emp; value = ready value }, ty)))
      | Axiom _ -> Val (Uninst (Neu { head; args = Emp; value = ready Unrealized }, ty)))
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
                   | Uninst (Neu _, (lazy ty)) -> { tm; ty }
                   | _ -> fatal (Anomaly "eval of lower-dim meta not neutral/canonical"));
             }) in
      match (Global.find_meta meta, ambient) with
      (* If an undefined potential metavariable appears in a case tree, then that branch of the case tree is stuck.  We don't need to return the metavariable itself; it suffices to know that that branch of the case tree is stuck, as the constant whose definition it is should handle all identity/equality checks correctly. *)
      | Metadef { tm = `None; _ }, Potential -> Unrealized
      (* To evaluate an undefined kinetic metavariable, we have to build a neutral. *)
      | Metadef { tm = `None; ty; _ }, Kinetic ->
          Val (Uninst (Neu { head; args = Emp; value = ready Unrealized }, lazy (make_ty meta ty)))
      (* If a metavariable has a definition that fits with the current energy, we simply evaluate that definition. *)
      | Metadef { tm = `Nonrec tm; energy = Potential; _ }, Potential -> eval env tm
      | Metadef { tm = `Nonrec tm; energy = Kinetic; _ }, Kinetic -> eval env tm
      | Metadef { tm = `Nonrec tm; energy = Kinetic; _ }, Potential -> Realize (eval_term env tm)
      | Metadef { tm = `Nonrec tm; energy = Potential; ty; _ }, Kinetic -> (
          if GluedEval.read () then
            (* A defined potential metavariable in kinetic context evaluates to a glued neutral, with its evaluated definition stored lazily. *)
            Val
              (Uninst (Neu { head; args = Emp; value = lazy_eval env tm }, lazy (make_ty meta ty)))
          else
            (* If a potential metavariable with a definition is used in a kinetic context, and doesn't evaluate yet to a kinetic result, we again have to build a neutral. *)
            match eval env tm with
            | Realize tm -> Val tm
            | value ->
                Val (Uninst (Neu { head; args = Emp; value = ready value }, lazy (make_ty meta ty)))
          ))
  | MetaEnv (meta, metaenv) ->
      let (Plus m_n) = D.plus (dim_term_env metaenv) in
      eval (eval_env env m_n metaenv) (Term.Meta (meta, Kinetic))
  | UU n ->
      let m = dim_env env in
      let (Plus mn) = D.plus n in
      Val (universe (D.plus_out m mn))
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
  | Lam (Variables (n, n_k, vars), body) ->
      let m = dim_env env in
      let (Plus m_nk) = D.plus (D.plus_out n n_k) in
      let (Plus m_n) = D.plus n in
      let mn_k = D.plus_assocl m_n n_k m_nk in
      Val (Lam (Variables (D.plus_out m m_n, mn_k, vars), eval_binder env m_nk body))
  | App (fn, args) ->
      (* First we evaluate the function. *)
      let efn = eval_term env fn in
      (* The environment is m-dimensional and the original application is n-dimensional, so the *substituted* application is m+n dimensional.  Thus must therefore match the dimension of the function being applied. *)
      let m = dim_env env in
      let n = CubeOf.dim args in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      (* Then we evaluate all the arguments, not just in the given environment (of dimension m), but in that environment acted on by all the strict faces of m.  Since the given arguments are indexed by strict faces of n, the result is a collection of values indexed by strict faces of m+n.  *)
      let eargs =
        CubeOf.build mn
          {
            build =
              (* Specifically, for each face of m+n... *)
              (fun fab ->
                (* ...we decompose it as a sum of a face "fa" of m and a face "fb" of n... *)
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                (* ...and evaluate the supplied argument indexed by the face fb of n, in an environment acted on by the face fa of m. *)
                eval_term (act_env env (op_of_sface fa)) (CubeOf.find args fb));
          } in
      (* Having evaluated the function and its arguments, we now pass the job off to a helper function. *)
      apply efn eargs
  | Field (tm, fld) -> field (eval_term env tm) fld
  | Struct (_, dim, fields, energy) ->
      let (Plus mn) = D.plus (dim_env env) in
      let ins = ins_zero (D.plus_out dim mn) in
      Val (Struct (Abwd.map (fun (tm, l) -> (lazy_eval env tm, l)) fields, ins, energy))
  | Constr (constr, n, args) ->
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      let eargs = List.map (eval_args env m_n mn) args in
      Val (Constr (constr, mn, eargs))
  | Pi (x, doms, cods) ->
      (* We are starting with an n-dimensional pi-type and evaluating it in an m-dimensional environment, producing an (m+n)-dimensional result. *)
      let n = CubeOf.dim doms in
      let m = dim_env env in
      let (Plus m_n) = D.plus n in
      let mn = D.plus_out m m_n in
      (* The basic thing we do is evaluate the cubes of domains and codomains. *)
      let doms =
        CubeOf.build mn
          {
            build =
              (fun fab ->
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                eval_term (act_env env (op_of_sface fa)) (CubeOf.find doms fb));
          } in
      let cods =
        BindCube.build mn
          {
            build =
              (fun fab ->
                let (SFace_of_plus (k_l, fa, fb)) = sface_of_plus m_n fab in
                eval_binder (act_env env (op_of_sface fa)) k_l (CodCube.find cods fb));
          } in
      (* However, because the result will be an Uninst, we need to know its type as well.  The starting n-dimensional pi-type (which is itself uninstantiated) lies in a full instantiation of the n-dimensional universe at lower-dimensional pi-types formed from subcubes of its domains and codomains.  Accordingly, the resulting (m+n)-dimensional pi-type will like in a full instantiation of the (m+n)-dimensional universe at lower-dimensional pi-types obtained by evaluating these at appropriately split faces.  Since each of them *also* belongs to a universe instantiated similarly, and needs to know its type not just because it is an uninst but because it is a normal, we build the whole cube at once and then take its top. *)
      let pitbl = Hashtbl.create 10 in
      let pis =
        CubeOf.build mn
          {
            build =
              (fun fab ->
                let kl = dom_sface fab in
                let ty =
                  inst (universe kl)
                    (TubeOf.build D.zero (D.zero_plus kl)
                       {
                         build =
                           (fun fc ->
                             Hashtbl.find pitbl (SFace_of (comp_sface fab (sface_of_tface fc))));
                       }) in
                let tm =
                  Uninst
                    (Pi (x, CubeOf.subcube fab doms, BindCube.subcube fab cods), Lazy.from_val ty)
                in
                let ntm = { tm; ty } in
                Hashtbl.add pitbl (SFace_of fab) ntm;
                ntm);
          } in
      Val (CubeOf.find_top pis).tm
  | Let (_, v, body) ->
      (* We evaluate let-bindings lazily, on the chance they aren't actually used. *)
      let args =
        CubeOf.build (dim_env env)
          { build = (fun fa -> lazy_eval (act_env env (op_of_sface fa)) v) } in
      eval (LazyExt (env, CubeOf.singleton args)) body
  (* It's tempting to write just "act_value (eval env x) s" here, but that is WRONG!  Pushing a substitution through an operator action requires whiskering the operator by the dimension of the substitution. *)
  | Act (x, s) ->
      let k = dim_env env in
      let (Plus km) = D.plus (dom_deg s) in
      let (Plus kn) = D.plus (cod_deg s) in
      let ks = plus_deg k kn km s in
      (* We push as much of the resulting degeneracy into the environment as possible, in hopes that the remaining insertion outside will be trivial and act_value will be able to short-circuit.  (Ideally, the insertion would be carried through by eval for a single traversal in all cases.) *)
      let (Insfact (fa, ins)) = insfact ks kn in
      Val (act_value (eval_term (act_env env (op_of_deg fa)) x) (perm_of_ins ins))
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
          | Some (Branch (plus, perm, body)) -> (
              match D.compare constr_dim total_dim with
              | Neq -> fatal (Dimension_mismatch ("evaluating match", constr_dim, total_dim))
              | Eq ->
                  (* If we have a branch with a matching constructor, then our constructor must be applied to exactly the right number of elements (in dargs).  In that case, we pick them out and add them to the environment. *)
                  let env = take_args env plus_dim dargs plus in
                  (* Then we proceed recursively with the body of that branch. *)
                  eval (Permute (perm, env)) body)
          (* If this constructor belongs to a refuted case, it must be that we are in an inconsistent context with some neutral belonging to an empty type.  In that case, the match must be stuck. *)
          | Some Refute -> Unrealized)
      (* Otherwise, the case tree doesn't reduce. *)
      | _ -> Unrealized)
  | Realize tm -> Realize (eval_term env tm)
  | Canonical c ->
      let (Any c) = eval_canonical env c in
      Canonical c

and eval_with_boundary :
    type m n mn a. (m, a) env -> (a, kinetic) term -> (m, kinetic value) CubeOf.t =
 fun env tm ->
  CubeOf.build (dim_env env) { build = (fun fa -> eval_term (act_env env (op_of_sface fa)) tm) }

(* A helper function that doesn't get the correct types if we define it inline. *)
and eval_args :
    type m n mn a.
    (m, a) env ->
    (m, n, mn) D.plus ->
    mn D.t ->
    (n, (a, kinetic) term) CubeOf.t ->
    (mn, kinetic value) CubeOf.t =
 fun env m_n mn tms ->
  CubeOf.build mn
    {
      build =
        (fun fab ->
          let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
          eval_term (act_env env (op_of_sface fa)) (CubeOf.find tms fb));
    }

(* Apply a function value to an argument (with its boundaries). *)
and apply : type n s. s value -> (n, kinetic value) CubeOf.t -> s evaluation =
 fun fn arg ->
  match view_term fn with
  (* If the function is a lambda-abstraction, we check that it has the correct dimension and then beta-reduce, adding the arguments to the environment. *)
  | Lam (_, body) -> (
      let m = CubeOf.dim arg in
      match D.compare (dim_binder body) m with
      | Neq -> fatal (Dimension_mismatch ("applying a lambda", dim_binder body, m))
      | Eq -> apply_binder body arg)
  (* If it is a neutral application... *)
  | Uninst (Neu { head; args; value }, (lazy ty)) -> (
      (* ... we check that it is fully instantiated... *)
      match view_type ty "apply" with
      | Pi (_, doms, cods, tyargs) -> (
          (* ... and that the pi-type and its instantiation have the correct dimension. *)
          let k = CubeOf.dim doms in
          match D.compare (CubeOf.dim arg) k with
          | Neq -> fatal (Dimension_mismatch ("applying a neutral function", CubeOf.dim arg, k))
          | Eq -> (
              (* We annotate the new argument by its type, extracted from the domain type of the function being applied. *)
              let newarg = norm_of_vals_cube arg doms in
              (* We compute the output type of the application. *)
              let newty = lazy (tyof_app cods tyargs arg) in
              (* We add the new argument to the existing application spine. *)
              let args = Snoc (args, App (Arg newarg, ins_zero k)) in
              if GluedEval.read () then
                (* We add the argument to the lazy value and return a glued neutral. *)
                let value = apply_lazy value newarg in
                Val (Uninst (Neu { head; args; value }, newty))
              else
                (* We evaluate further with a case tree. *)
                match force_eval value with
                | Unrealized -> Val (Uninst (Neu { head; args; value = ready Unrealized }, newty))
                | Val tm -> (
                    match apply tm arg with
                    | Realize x -> Val x
                    | Canonical (Data d) ->
                        let newtm =
                          Uninst (Neu { head; args; value = ready (Canonical (Data d)) }, newty)
                        in
                        if Option.is_none !(d.tyfam) then
                          d.tyfam := Some (lazy { tm = newtm; ty = Lazy.force newty });
                        Val newtm
                    | value -> Val (Uninst (Neu { head; args; value = ready value }, newty)))
                | Canonical
                    (Data { dim; tyfam; indices = Unfilled _ as indices; constrs; discrete }) -> (
                    match D.compare dim k with
                    | Neq -> fatal (Dimension_mismatch ("apply", dim, k))
                    | Eq ->
                        let indices = Fillvec.snoc indices newarg in
                        let value =
                          Value.Canonical (Data { dim; tyfam; indices; constrs; discrete }) in
                        Val (Uninst (Neu { head; args; value = ready value }, newty)))
                | _ -> fatal (Anomaly "invalid application of type")))
      | _ -> fatal (Anomaly "invalid application by non-function"))
  | _ -> fatal (Anomaly "invalid application of non-function")

(* Compute the output type of a function application, given the codomains and instantiation arguments of the pi-type (the latter being the functions acting on the boundary) and the arguments it is applied to. *)
and tyof_app :
    type k.
    (k, unit) BindCube.t ->
    (D.zero, k, k, normal) TubeOf.t ->
    (k, kinetic value) CubeOf.t ->
    kinetic value =
 fun cods fns args ->
  let out_arg_tbl = Hashtbl.create 10 in
  let out_args =
    TubeOf.mmap
      {
        map =
          (fun fa [ { tm = afn; ty = _ } ] ->
            let fa = sface_of_tface fa in
            let tmargs = CubeOf.subcube fa args in
            let tm = apply_term afn tmargs in
            let cod = apply_binder_term (BindCube.find cods fa) tmargs in
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
  inst (apply_binder_term (BindCube.find_top cods) args) out_args

(* Compute a field of a structure. *)
and field : type n s. s value -> Field.t -> s evaluation =
 fun tm fld ->
  match view_term tm with
  (* TODO: Is it okay to ignore the insertion here?  I'm currently assuming that it must be zero if this field projection is well-typed. *)
  | Struct (fields, _, energy) -> (
      match (Abwd.find_opt fld fields, energy) with
      | Some xv, _ -> force_eval (fst xv)
      | None, Potential -> Unrealized
      | None, Kinetic -> fatal (Anomaly ("missing field in eval struct: " ^ Field.to_string fld)))
  | Uninst (Neu { head; args; value }, (lazy ty)) -> (
      let Wrap n, newty = tyof_field_withdim tm ty fld in
      let newty = Lazy.from_val newty in
      let args = Snoc (args, App (Field fld, ins_zero n)) in
      if GluedEval.read () then
        let value = field_lazy value fld in
        Val (Uninst (Neu { head; args; value }, newty))
      else
        match force_eval value with
        | Unrealized -> Val (Uninst (Neu { head; args; value = ready Unrealized }, newty))
        | Val tm -> (
            match field tm fld with
            | Realize x -> Val x
            | Canonical (Data d) ->
                let newtm = Uninst (Neu { head; args; value = ready (Canonical (Data d)) }, newty) in
                if Option.is_none !(d.tyfam) then
                  d.tyfam := Some (lazy { tm = newtm; ty = Lazy.force newty });
                Val newtm
            | value -> Val (Uninst (Neu { head; args; value = ready value }, newty)))
        | Canonical _ -> fatal (Anomaly "field projection of canonical type")
        | Realize _ -> fatal (Anomaly "realized neutral"))
  | _ -> fatal ~severity:Asai.Diagnostic.Bug (No_such_field (`Other, `Name fld))

and field_term : type n. kinetic value -> Field.t -> kinetic value =
 fun x fld ->
  let (Val v) = field x fld in
  v

(* Given a term and its record type, compute the type and dimension of a field projection.  The caller can control the severity of errors, depending on whether we're typechecking (Error) or normalizing (Bug, the default). *)
and tyof_field_withname ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.or_index) :
    Field.t * dim_wrapped * kinetic value =
  match view_type ?severity ty "tyof_field" with
  | Canonical (head, Codata { env; ins; fields; opacity = _; eta = _ }, tyargs) -> (
      (* The type cannot have a nonidentity degeneracy applied to it (though it can be at a higher dimension). *)
      if Option.is_none (is_id_ins ins) then
        fatal ?severity (No_such_field (`Degenerated_record, fld));
      let m = cod_left_ins ins in
      let n = cod_right_ins ins in
      let mn = plus_of_ins ins in
      let mn' = D.plus_out m mn in
      match D.compare (TubeOf.inst tyargs) mn' with
      | Neq ->
          fatal ?severity (Dimension_mismatch ("computing type of field", TubeOf.inst tyargs, mn'))
      | Eq -> (
          (* The type of the field projection comes from the type associated to that field name in general, evaluated at the stored environment extended by the term itself and its boundaries. *)
          let tyargs' = TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm) in
          let entries =
            CubeOf.build n
              {
                build =
                  (fun fb ->
                    CubeOf.build m
                      {
                        build =
                          (fun fa ->
                            let (Plus pq) = D.plus (dom_sface fb) in
                            CubeOf.find tyargs' (sface_plus_sface fa mn pq fb));
                      });
              } in
          let env = Value.Ext (env, entries) in
          match Field.find fields fld with
          | Some (fldname, fldty) ->
              ( fldname,
                Wrap m,
                (* This type is m-dimensional, hence must be instantiated at a full m-tube. *)
                inst (eval_term env fldty)
                  (TubeOf.mmap
                     {
                       map =
                         (fun _ [ arg ] ->
                           let (Val tm) = field arg.tm fldname in
                           let _, _, ty = tyof_field_withname arg.tm arg.ty fld in
                           { tm; ty });
                     }
                     [ TubeOf.middle (D.zero_plus m) mn tyargs ]) )
          | None -> fatal ?severity (No_such_field (`Record (phead head), fld))))
  | _ -> fatal ?severity (No_such_field (`Other, fld))

and tyof_field_withdim ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.t) :
    dim_wrapped * kinetic value =
  let _, n, ty = tyof_field_withname ?severity tm ty (`Name fld) in
  (n, ty)

and tyof_field ?severity (tm : kinetic value) (ty : kinetic value) (fld : Field.t) : kinetic value =
  let _, _, ty = tyof_field_withname ?severity tm ty (`Name fld) in
  ty

and eval_binder :
    type m n mn b s.
    (m, b) env -> (m, n, mn) D.plus -> ((b, n) snoc, s) term -> (mn, s) Value.binder =
 fun env mn body ->
  let m = dim_env env in
  let n = D.plus_right mn in
  let (Id_ins ins) = id_ins m n in
  let Eq = D.plus_uniq mn (plus_of_ins ins) in
  Value.Bind { env; ins; body }

and apply_binder : type n s. (n, s) Value.binder -> (n, kinetic value) CubeOf.t -> s evaluation =
 fun (Value.Bind { env; ins; body }) argstbl ->
  let m = dim_env env in
  let n = cod_right_ins ins in
  let mn = plus_of_ins ins in
  let perm = perm_of_ins ins in
  (* The arguments have to be acted on by degeneracies to form the appropriate cube.  But not all the arguments may be actually used, so we do these actions lazily. *)
  act_evaluation
    (eval
       (LazyExt
          ( env,
            CubeOf.build n
              {
                build =
                  (fun fs ->
                    CubeOf.build m
                      {
                        build =
                          (fun fr ->
                            let (Plus kj) = D.plus (dom_sface fs) in
                            let frfs = sface_plus_sface fr mn kj fs in
                            let (Face (fa, fb)) = perm_sface (perm_inv perm) frfs in
                            act_lazy_eval (defer (fun () -> Val (CubeOf.find argstbl fa))) fb);
                      });
              } ))
       body)
    perm

and eval_canonical : type m a. (m, a) env -> a Term.canonical -> any_canonical =
 fun env can ->
  match can with
  | Data { indices; constrs; discrete } ->
      let tyfam = ref None in
      let constrs =
        Abwd.map
          (fun (Term.Dataconstr { args; indices }) -> Value.Dataconstr { env; args; indices })
          constrs in
      Any (Data { dim = dim_env env; tyfam; indices = Fillvec.empty indices; constrs; discrete })
  | Codata { eta; opacity; dim; fields } ->
      let (Id_ins ins) = id_ins (dim_env env) dim in
      Any (Codata { eta; opacity; env; ins; fields })

and eval_term : type m b. (m, b) env -> (b, kinetic) term -> kinetic value =
 fun env tm ->
  let (Val v) = eval env tm in
  v

and eval_env :
    type a m n mn b. (m, a) env -> (m, n, mn) D.plus -> (a, n, b) Term.env -> (mn, b) Value.env =
 fun env m_n tmenv ->
  let mn = D.plus_out (dim_env env) m_n in
  match tmenv with
  | Emp _ -> Emp mn
  | Ext (tmenv, xss) ->
      (* We make everything lazy, since we can, and not everything may end up being used. *)
      LazyExt
        ( eval_env env m_n tmenv,
          CubeOf.mmap
            {
              map =
                (fun _ [ xs ] ->
                  CubeOf.build mn
                    {
                      build =
                        (fun fab ->
                          let (SFace_of_plus (_, fa, fb)) = sface_of_plus m_n fab in
                          lazy_eval (act_env env (op_of_sface fa)) (CubeOf.find xs fb));
                    });
            }
            [ xss ] )

and apply_term : type n. kinetic value -> (n, kinetic value) CubeOf.t -> kinetic value =
 fun fn arg ->
  let (Val v) = apply fn arg in
  v

and apply_binder_term : type n. (n, kinetic) binder -> (n, kinetic value) CubeOf.t -> kinetic value
    =
 fun b arg ->
  let (Val v) = apply_binder b arg in
  v

and force_eval : type s. s lazy_eval -> s evaluation =
 fun lev ->
  match !lev with
  | Deferred_eval (env, tm, ins, apps) ->
      (* TODO: In an ideal world, there would be one function that would traverse the term once doing both "eval" and "act" by the insertion. *)
      let etm = act_evaluation (eval env tm) (perm_of_ins ins) in
      let etm = Bwd.fold_left app_eval etm apps in
      lev := Ready etm;
      etm
  | Deferred (tm, s, apps) ->
      let etm = act_evaluation (tm ()) s in
      let etm = Bwd.fold_left app_eval etm apps in
      lev := Ready etm;
      etm
  | Ready etm -> etm

and force_eval_term : kinetic lazy_eval -> kinetic value =
 fun v ->
  let (Val v) = force_eval v in
  v

(* Apply something to an 'app', calling either 'apply' or 'field'. *)
and app_eval : type s. s evaluation -> app -> s evaluation =
 fun ev x ->
  let app : type s. s value -> app -> s evaluation =
   fun tm x ->
    match x with
    | App (Arg xs, ins) -> act_evaluation (apply tm (val_of_norm_cube xs)) (perm_of_ins ins)
    | App (Field fld, ins) -> act_evaluation (field tm fld) (perm_of_ins ins) in
  match (ev, x) with
  | Val v, _ -> app v x
  | Realize v, _ ->
      let (Val v) = app v x in
      Realize v
  | Unrealized, _ -> Unrealized
  | ( Canonical (Data { dim; tyfam; indices = Unfilled _ as indices; constrs; discrete }),
      App (Arg arg, ins) ) -> (
      match (D.compare dim (CubeOf.dim arg), is_id_ins ins) with
      | Neq, _ -> fatal (Dimension_mismatch ("adding indices to a datatype", dim, CubeOf.dim arg))
      | _, None -> fatal (Anomaly "nonidentity insertion on datatype")
      | Eq, Some () ->
          let indices = Fillvec.snoc indices arg in
          Canonical (Data { dim; tyfam; indices; constrs; discrete }))
  | Canonical _, _ -> fatal (Anomaly "app on canonical type")

(* Look up a cube of values in an environment by variable index, accumulating operator actions as we go.  Eventually we will usually use the operator to select a value from the cubes and act on it, but we can't do that until we've defined acting on a value by a degeneracy (unless we do open recursive trickery). *)
and lookup_cube :
    type m n k a b. (n, b) env -> (a, k, b) Tbwd.insert -> (m, n) op -> (m, k) looked_up_cube =
 fun env v op ->
  match (env, v) with
  (* Since there's an index, the environment can't be empty. *)
  | Emp _, _ -> .
  (* If we encounter an operator action, we accumulate it. *)
  | Act (env, op'), _ -> lookup_cube env v (comp_op op' op)
  (* If the environment is permuted, we apply the permutation to the index. *)
  | Permute (p, env), v ->
      let (Permute_insert (v, _)) = Tbwd.permute_insert v p in
      lookup_cube env v op
  (* If we encounter a variable that isn't ours, we skip it and proceed. *)
  | Ext (env, _), Later v -> lookup_cube env v op
  | LazyExt (env, _), Later v -> lookup_cube env v op
  (* Finally, when we find our variable, we decompose the accumulated operator into a strict face and degeneracy, use the face as an index lookup, and act by the degeneracy.  The forcing function is the identity if the entry is not lazy, and force_eval_term if it is lazy. *)
  | Ext (_, entry), Now -> Looked_up ((fun x -> x), op, entry)
  | LazyExt (_, entry), Now -> Looked_up (force_eval_term, op, entry)

and lookup : type n b. (n, b) env -> b Term.index -> kinetic value =
 fun env (Index (v, fa)) ->
  let (Looked_up (force, Op (f, s), entry)) = lookup_cube env v (id_op (dim_env env)) in
  match D.compare (cod_sface fa) (CubeOf.dim entry) with
  | Eq -> act_value (force (CubeOf.find (CubeOf.find entry fa) f)) s
  | Neq -> fatal (Dimension_mismatch ("lookup", cod_sface fa, CubeOf.dim entry))

(* Instantiate an arbitrary value, combining tubes. *)
and inst : type m n mn. kinetic value -> (m, n, mn, normal) TubeOf.t -> kinetic value =
 fun tm args2 ->
  let n = TubeOf.inst args2 in
  match D.compare_zero n with
  | Zero -> tm
  | Pos dim2 -> (
      match view_term tm with
      | Inst { tm; dim = _; args = args1; tys = tys1 } -> (
          match D.compare (TubeOf.out args2) (TubeOf.uninst args1) with
          | Neq ->
              fatal
                (Dimension_mismatch
                   ( "instantiating a partially instantiated type",
                     TubeOf.out args2,
                     TubeOf.uninst args1 ))
          | Eq ->
              let (Plus nk) = D.plus (TubeOf.inst args1) in
              let args = TubeOf.plus_tube nk args1 args2 in
              let tys = TubeOf.middle (D.zero_plus (TubeOf.uninst args2)) (TubeOf.plus args2) tys1 in
              let tys = inst_args args2 tys in
              Inst { tm; dim = D.pos_plus dim2 nk; args; tys })
      | Uninst (tm, (lazy ty)) -> (
          (* In this case, the type must be a fully instantiated universe of the right dimension, and the remaining types come from its instantiation arguments. *)
          match view_type ty "inst" with
          | UU tyargs -> (
              match D.compare (TubeOf.inst tyargs) (TubeOf.out args2) with
              | Neq ->
                  fatal
                    (Dimension_mismatch
                       ("instantiating an uninstantiated type", TubeOf.out tyargs, TubeOf.out args2))
              | Eq ->
                  let tys =
                    val_of_norm_tube
                      (TubeOf.middle (D.zero_plus (TubeOf.uninst args2)) (TubeOf.plus args2) tyargs)
                  in
                  let tys = inst_args args2 tys in
                  Inst { tm; dim = dim2; args = args2; tys })
          | _ -> fatal (Anomaly "can't instantiate non-type"))
      | Lam _ -> fatal (Anomaly "can't instantiate lambda-abstraction")
      | Struct _ -> fatal (Anomaly "can't instantiate struct")
      | Constr _ -> fatal (Anomaly "can't instantiate constructor"))

and inst_args :
    type m n mn.
    (m, n, mn, normal) TubeOf.t ->
    (D.zero, m, m, kinetic value) TubeOf.t ->
    (D.zero, m, m, kinetic value) TubeOf.t =
 fun args2 tys ->
  let n = TubeOf.inst args2 in
  TubeOf.mmap
    {
      map =
        (fun fe [ ty ] ->
          let j = dom_tface fe in
          let (Plus jn) = D.plus n in
          let args =
            TubeOf.build j jn
              {
                build =
                  (fun fa ->
                    let (PFace_of_plus (pq, fc, fd)) = pface_of_plus fa in
                    let fec = comp_sface (sface_of_tface fe) fc in
                    let fecd = sface_plus_pface fec (TubeOf.plus args2) pq fd in
                    TubeOf.find args2 fecd);
              } in
          inst ty args);
    }
    [ tys ]

(* Given a *type*, hence an element of a fully instantiated universe, extract the arguments of the instantiation of that universe.  These were stored in the extra arguments of Uninst and Inst. *)
and inst_tys : kinetic value -> kinetic value full_tube = function
  | Uninst (_, (lazy (Uninst (UU z, _)))) -> (
      match D.compare z D.zero with
      | Eq -> Full_tube (TubeOf.empty D.zero)
      | Neq -> fatal (Anomaly "higher universe must be instantiated to be a type"))
  | Uninst (_, (lazy (Inst { tm = UU _; dim = _; args = tys; tys = _ }))) -> (
      match D.compare (TubeOf.uninst tys) D.zero with
      | Eq ->
          let Eq = D.plus_uniq (D.zero_plus (TubeOf.inst tys)) (TubeOf.plus tys) in
          Full_tube (val_of_norm_tube tys)
      | Neq -> fatal (Anomaly "universe must be fully instantiated to be a type"))
  | Inst { tm = _; dim = _; args = _; tys } -> Full_tube tys
  | _ -> fatal (Anomaly "invalid type, has no instantiation arguments")

(* Given two families of values, the second intended to be the types of the other, annotate the former by instantiations of the latter to make them into normals.  Since we have to instantiate the types at the *normal* version of the terms, which is what we are computing, we also add the results to a hashtable as we create them so we can access them randomly later.  And since we have to do this sometimes with cubes and sometimes with tubes, we first define the content of the operation as a helper function. *)

and norm_of_val :
    type m n.
    (n sface_of, normal) Hashtbl.t -> (m, n) sface -> kinetic value -> kinetic value -> normal =
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

and norm_of_vals_cube :
    type k. (k, kinetic value) CubeOf.t -> (k, kinetic value) CubeOf.t -> (k, normal) CubeOf.t =
 fun tms tys ->
  let new_tm_tbl = Hashtbl.create 10 in
  CubeOf.mmap { map = (fun fab [ tm; ty ] -> norm_of_val new_tm_tbl fab tm ty) } [ tms; tys ]

and norm_of_vals_tube :
    type n k nk.
    (n, k, nk, kinetic value) TubeOf.t ->
    (n, k, nk, kinetic value) TubeOf.t ->
    (n, k, nk, normal) TubeOf.t =
 fun tms tys ->
  let new_tm_tbl = Hashtbl.create 10 in
  TubeOf.mmap
    { map = (fun fab [ tm; ty ] -> norm_of_val new_tm_tbl (sface_of_tface fab) tm ty) }
    [ tms; tys ]

(* Apply a function to all the values in a cube one by one as 0-dimensional applications, rather than as one n-dimensional application. *)
let apply_singletons : type n. kinetic value -> (n, kinetic value) CubeOf.t -> kinetic value =
 fun fn xs ->
  let module MC = CubeOf.Monadic (Monad.State (struct
    type t = kinetic value
  end)) in
  snd (MC.miterM { it = (fun _ [ x ] fn -> ((), apply_term fn (CubeOf.singleton x))) } [ xs ] fn)

(* Evaluate a term context to produce a value context. *)

let eval_bindings :
    type a b n.
    (a, b) Ctx.Ordered.t -> (n, (b, n) snoc Termctx.binding) CubeOf.t -> (n, Ctx.Binding.t) CubeOf.t
    =
 fun ctx cbs ->
  let open Termctx in
  let i = Ctx.Ordered.length ctx in
  let vbs = CubeOf.build (CubeOf.dim cbs) { build = (fun _ -> Ctx.Binding.unknown ()) } in
  let tempctx = Ctx.Ordered.Snoc (ctx, Invis vbs, Zero) in
  let argtbl = Hashtbl.create 10 in
  let j = ref 0 in
  let () =
    CubeOf.miter
      {
        it =
          (fun fa [ ({ ty = cty; tm = ctm } : (b, n) snoc binding); vb ] ->
            (* Unlike in dom_vars, we don't need to instantiate the types, since their instantiations should have been preserved by readback and will reappear correctly here. *)
            let ety = eval_term (Ctx.Ordered.env tempctx) cty in
            let level = (i, !j) in
            j := !j + 1;
            let v =
              match ctm with
              | None -> ({ tm = var level ety; ty = ety } : normal)
              | Some ctm -> { tm = eval_term (Ctx.Ordered.env tempctx) ctm; ty = ety } in
            Hashtbl.add argtbl (SFace_of fa) v;
            Ctx.Binding.specify vb None v);
      }
      [ cbs; vbs ] in
  vbs

let eval_entry : type a b f n. (a, b) Ctx.Ordered.t -> (b, f, n) Termctx.entry -> (f, n) Ctx.entry =
 fun ctx e ->
  match e with
  | Termctx.Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus } ->
      let bindings = eval_bindings ctx bindings in
      let fields = Bwv.map (fun (f, x, _) -> (f, x)) fields in
      Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus }
  | Invis bindings -> Invis (eval_bindings ctx bindings)

let rec eval_ordered_ctx : type a b. (a, b) Termctx.ordered -> (a, b) Ctx.Ordered.t = function
  | Termctx.Emp -> Emp
  | Snoc (ctx, e, af) ->
      let ectx = eval_ordered_ctx ctx in
      Snoc (ectx, eval_entry ectx e, af)
  | Lock ctx -> Lock (eval_ordered_ctx ctx)

let eval_ctx : type a b. (a, b) Termctx.t -> (a, b) Ctx.t = function
  | Termctx.Permute (p, ctx) ->
      let ctx = eval_ordered_ctx ctx in
      Permute (p, Ctx.Ordered.env ctx, ctx)

(* Given a type belonging to the m+n dimensional universe instantiated at tyargs, compute the instantiation of the m-dimensional universe that its instantiation belongs to. *)
let rec tyof_inst :
    type m n mn. (D.zero, mn, mn, normal) TubeOf.t -> (m, n, mn, normal) TubeOf.t -> kinetic value =
 fun tyargs eargs ->
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
            let ty = tyof_inst jntyargs jnargs in
            { tm; ty });
      } in
  inst (universe m) margs

(* Check whether a given type should be considered as discrete in the current typechecking context.  This means it is either: *)
let is_discrete : kinetic value -> bool =
 fun ty ->
  match view_type ty "is_discrete" with
  (* 1. A previously defined discrete type, or *)
  | Canonical (_, Data { discrete = true; _ }, _) -> true
  (* 2. The type currently being defined, at dimension zero.  Note that the *value* of this type in the Discrete map will be false, since we haven't *yet* decided that it *is* discrete; so we use 'mem' rather than 'find' to just check that it *is* currently being defined.  *)
  (* TODO: In a mutual block, this is not the correct test: it considers all the mutually defined types to be "discrete" even if they don't later turn out to be.  At present we are disallowing discreteness for all mutual families. *)
  | Canonical (Const { name; _ }, _, tyargs) when Constant.Map.mem name (Discrete.get ()) -> (
      match D.compare (TubeOf.inst tyargs) D.zero with
      | Eq -> true
      | Neq -> false)
  (* In theory, pi-types with discrete codomain, and record types with discrete fields, could also be discrete.  But that would be trickier to check as it would require evaluating their codomain and fields under binders, and eta-conversion for those types should implement direct discreteness automatically.  So the only thing we're missing is that they can't appear as arguments to a constructor of some other discrete datatype. *)
  | _ -> false

let () = Act.forward_view_term := view_term
