open Util
open Reporter
open Printable
open Dim
open Term
open Value
open Domvars
open Norm
open Act
open Readback
module Err = Monad.Error (Unequal)
open Monad.Ops (Err)

let guard test err = if test then Ok () else Error err
let fail err = Error err

let if_known (test : 'a Err.t option) err =
  match test with
  | None -> Error (err ())
  | Some x -> x

let ok = Ok ()

module ErrOpt = struct
  type 'a t = 'a Err.t option

  let return x = Some (Ok x)

  let bind x f =
    match x with
    | None -> None
    | Some (Error err) -> Some (Error err)
    | Some (Ok x) -> f x

  let of_opt = function
    | None -> None
    | Some () -> Some (Ok ())
end

module ListM = Mlist.Monadic (Err)
module BwdM = Mbwd.Monadic (Err)

(* Eta-expanding equality checks.  In all functions, the integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

module Mode = Algaeff.Reader.Make (struct
  type t = [ `Rigid | `Full ]
end)

let () = Mode.register_printer (function `Read -> Some "unhandled Equal.Mode.read effect")

module Equal = struct
  (* Compare two normal forms that are *assumed* to have the same type, or at least that the type of the first is a subtype of the type of the second. *)
  let rec equal_nf : type a b. (a, b) Ctx.t -> normal -> normal -> unit Err.t =
   fun n x y ->
    (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  We check them at the type of the *second* argument, since this is also called as a subroutine of subtype checking, in which case the subtype comes first and then the supertype. *)
    equal_at n x.tm y.tm y.ty

  (* Compare two values at a type, which they are both assumed to belong to.  We do eta-expansion here if the type is one with an eta-rule, like a pi-type or a record type.  We also deal with the case of terms that don't synthesize, such as structs even in codatatypes without eta, and constructors in datatypes. *)
  and equal_at : type a b.
      (a, b) Ctx.t -> kinetic value -> kinetic value -> kinetic value -> unit Err.t =
   fun ctx x y ty ->
    (* The type must be fully instantiated. *)
    match view_type ty "equal_at" with
    (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
    | Canonical (_, Pi (name, doms, cods), ins, tyargs) ->
        let Eq = eq_of_ins_zero ins in
        let newargs, newnfs = dom_vars ctx doms in
        let (Any_ctx newctx) = Ctx.variables_vis ctx name newnfs in
        let output = tyof_app cods tyargs newargs in
        (* If both terms have the given pi-type, then when applied to variables of the domains, they will both have the computed output-type, so we can recurse back to eta-expanding equality at that type. *)
        equal_at newctx (apply_term x newargs) (apply_term y newargs) output
    (* Codatatypes (without eta) don't need to be dealt with here, even though structs can't be compared synthesizingly, since codatatypes aren't actually inhabited by (kinetic) structs, only neutral terms that are equal to potential structs.  In the case of record types with eta, if there is a nonidentity insertion outside, then the type isn't actually a record type, *but* it still has an eta-rule since it is *isomorphic* to a record type!  Thus, instead of checking whether the insertion is the identity, we apply its inverse permutation to the terms being compared.  And because we pass off to 'field' and 'tyof_field', we don't need to make explicit use of any of the other data here. *)
    | Canonical
        (type mn m n)
        ((_, Codata (type c a et) ({ eta; fields; _ } : (m, n, c, a, et) codata_args), ins, _) :
          head * (m, n) canonical * (mn, m, n) insertion * (D.zero, mn, mn, normal) TubeOf.t) -> (
        match eta with
        | Eta ->
            let (Perm_to p) = perm_of_ins ins in
            let pinv = deg_of_perm (perm_inv p) in
            let x, y, ty = (act_value x pinv, act_value y pinv, gact_ty None ty pinv) in
            (* Now we take the projections and compare them at appropriate types.  It suffices to use the fields of x when computing the types of the fields, since we proceed to check the fields for equality *in order* and thus by the time we are checking equality of any particular field of x and y, the previous fields of x and y are already known to be equal, and the type of the current field can only depend on these.  (This latter is a semantic constraint on the kinds of generalized records that can sensibly admit eta-conversion.)  In addition, records with eta cannot have higher fields, so as field insertion it suffices to use ins_zero on the substitution dimension. *)
            let fldins = ins_zero (cod_left_ins ins) in
            BwdM.miterM
              (fun [
                     CodatafieldAbwd.Entry
                       (type i)
                       ((fld, Lower _) : i Field.t * (i, a * n * has_eta) Codatafield.t);
                   ] ->
                equal_at ctx (field_term x fld fldins) (field_term y fld fldins)
                  (tyof_field (Ok x) ty fld ~shuf:Trivial fldins))
              [ fields ]
        (* At a codatatype without eta, there are no kinetic structs, only comatches, and those are not compared componentwise, only as neutrals, since they are generative. *)
        | Noeta -> equal_val ctx x y)
    (* At a higher-dimensional version of a discrete datatype, any two terms are equal.  Note that we do not check here whether discreteness is on: that affects datatypes when they are *defined*, not when they are used. *)
    | Canonical (_, Data { dim; discrete = `Yes; _ }, _, _) when is_pos dim -> return ()
    (* At an ordinary datatype, two constructors are equal if they are instances of the same constructor, with the same dimension and arguments.  We handle these cases here because we can use the datatype information to give types to the arguments of the constructor. *)
    | Canonical (_, Data { constrs; _ }, _, tyargs) -> (
        let x, y =
          match Mode.read () with
          | `Rigid -> (x, y)
          | `Full -> (view_term x, view_term y) in
        match (x, y) with
        | Constr (xconstr, xn, xargs), Constr (yconstr, yn, yargs) -> (
            let (Dataconstr { env; args = argtys; indices = _ }) =
              match Abwd.find_opt xconstr constrs with
              | Some x -> x
              | None -> fatal (Anomaly "constr not found in equality-check") in
            let* () = guard (xconstr = yconstr) (Unequal.Constrs (xconstr, yconstr)) in
            match
              ( D.compare xn yn,
                D.compare xn (TubeOf.inst tyargs),
                D.compare (TubeOf.inst tyargs) (dim_env env) )
            with
            | Neq, _, _ -> fatal (Dimension_mismatch ("equality of constrs", xn, yn))
            | _, Neq, _ ->
                fatal (Dimension_mismatch ("equality of constrs", xn, TubeOf.inst tyargs))
            | _, _, Neq ->
                fatal
                  (Dimension_mismatch ("equality at canonical", TubeOf.inst tyargs, dim_env env))
            | Eq, Eq, Eq ->
                (* The instantiation must be at other instances of the same constructor; we take its arguments as in 'check'. *)
                let tyarg_args =
                  TubeOf.mmap
                    {
                      map =
                        (fun _ [ tm ] ->
                          match view_term tm.tm with
                          | Constr (tmname, _, tmargs) ->
                              if tmname = xconstr then List.map (fun a -> CubeOf.find_top a) tmargs
                              else fatal (Anomaly "inst arg wrong constr in equality at datatype")
                          | _ -> fatal (Anomaly "inst arg not constr in equality at datatype"));
                    }
                    [ tyargs ] in
                (* It suffices to compare the top-dimensional faces of the cubes; the others are only there for evaluating case trees.  It would be nice to do this recursion directly on the Bwds, but equal_at_tel is expressed much more cleanly as an operation on lists. *)
                equal_at_tel ctx env
                  (List.fold_right (fun a args -> CubeOf.find_top a :: args) xargs [])
                  (List.fold_right (fun a args -> CubeOf.find_top a :: args) yargs [])
                  argtys
                  (TubeOf.mmap { map = (fun _ [ args ] -> args) } [ tyarg_args ]))
        | Constr _, _ | _, Constr _ ->
            fail (Unequal.Terms (PNormal (ctx, { tm = x; ty }), PNormal (ctx, { tm = y; ty })))
        | _ -> equal_val ctx x y)
    (* If the type is not one that has an eta-rule, then we pass off to a synthesizing equality-check, forgetting about our assumption that the two terms had the same type.  This is the equality-checking analogue of the conversion rule for checking a synthesizing term, but since equality requires no evidence we don't have to actually synthesize a type at which they are equal or verify that it equals the type we assumed them to have. *)
    | _ -> equal_val ctx x y

  (* "Synthesizing" equality check of two values, now *not* assumed a priori to have the same type.  If this function concludes that they are equal, then the equality of their types is part of that conclusion. *)
  and equal_val : type a b. (a, b) Ctx.t -> kinetic value -> kinetic value -> unit Err.t =
   fun ctx x y ->
    let x, y =
      match Mode.read () with
      | `Rigid -> (x, y)
      | `Full -> (view_term x, view_term y) in
    match (x, y) with
    | ( Neu { head = head1; args = apps1; value = _; ty = _ },
        Neu { head = head2; args = apps2; value = _; ty = _ } ) -> (
        (* To check two neutral applications are equal, with their types, we first check if the functions are equal, including their types and hence also their domains and codomains (and also they have the same insertion applied outside).  An alignment doesn't affect definitional equality.  We don't need to check that the types agree; this procedure concludes equality of types rather than assumes it. *)
        match equal_head ctx head1 head2 with
        | Some (Error err) -> Error (Unequal.Heads err)
        | None ->
            let h1, h2 = (readback_head ctx head1, readback_head ctx head2) in
            Error (Unequal.Heads (Terms (PTerm (ctx, h1), PTerm (ctx, h2))))
        | Some (Ok ()) -> (
            match equal_apps ctx apps1 apps2 with
            | None -> Error (Unequal.Terms (PVal (ctx, x), PVal (ctx, y)))
            | Some x -> x))
    | Lam _, _ | _, Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing equality-check")
    | Struct _, _ | _, Struct _ ->
        fatal (Anomaly "unexpected struct in synthesizing equality-check")
    | Constr _, _ | _, Constr _ ->
        fatal (Anomaly "unexpected constr in synthesizing equality-check")

  and equal_tyargs : type n1 k1 nk1 n2 k2 nk2 a b.
      (a, b) Ctx.t ->
      (n1, k1, nk1, normal) TubeOf.t ->
      (n2, k2, nk2, normal) TubeOf.t ->
      unit ErrOpt.t =
   fun n a1 a2 ->
    match
      (D.compare (TubeOf.inst a1) (TubeOf.inst a2), D.compare (TubeOf.uninst a1) (TubeOf.uninst a2))
    with
    | Eq, Eq ->
        let Eq = D.plus_uniq (TubeOf.plus a1) (TubeOf.plus a2) in
        let open TubeOf.Monadic (Err) in
        (* Because instantiation arguments are stored as normals, we use type-sensitive equality to compare them. *)
        Some (miterM { it = (fun _ [ x; y ] -> equal_nf n x y) } [ a1; a2 ])
    | Neq, _ -> None
    | _, Neq -> None

  (* Synthesizing equality check for heads.  Again equality of types is part of the conclusion, not a hypothesis.  If some sub-parts of the heads are unequal, such as arguments of a Pi, or variable or constant names (without degeneracies), we report that.  Otherwise, we return None, and the caller should report the entire heads as being unequal. *)
  and equal_head : type a b. (a, b) Ctx.t -> head -> head -> unit ErrOpt.t =
   fun ctx x y ->
    let open Monad.Ops (ErrOpt) in
    match (x, y) with
    | Var { level = l1; deg = d1 }, Var { level = l2; deg = d2 } ->
        (* Two equal variables with the same degeneracy applied are equal, including their types because that variable has only one type. *)
        if l1 = l2 then if Option.is_some (deg_equiv d1 d2) then return () else None
        else
          let v1 = Ctx.find_level ctx l1 <|> No_such_level (PLevel l1) in
          let v2 = Ctx.find_level ctx l2 <|> No_such_level (PLevel l2) in
          Some (Error (Variables (PTerm (ctx, Var v1), PTerm (ctx, Var v2))))
    | Const { name = c1; ins = i1 }, Const { name = c2; ins = i2 } -> (
        let* () = Some (guard (c1 = c2) (Unequal.Constants (c1, c2))) in
        match D.compare (cod_left_ins i1) (cod_left_ins i2) with
        | Eq ->
            let To d1, To d2 = (deg_of_ins i1, deg_of_ins i2) in
            let* () = ErrOpt.of_opt (deg_equiv d1 d2) in
            return ()
        | Neq -> None)
    | Meta { meta = meta1; env = env1; ins = i1 }, Meta { meta = meta2; env = env2; ins = i2 } -> (
        match (Meta.compare meta1 meta2, D.compare (cod_left_ins i1) (cod_left_ins i2)) with
        | Eq, Eq -> Some (equal_env ctx env1 env2 (Global.find_meta meta1).termctx)
        | Neq, _ -> Some (Error (Metas (meta1, meta2)))
        | _, Neq -> None)
    | UU m, UU n -> (
        (* Two universes are equal precisely when they have the same dimension, in which case they also automatically have the same type (a standard instantiation of a (higher) universe of that same dimension). *)
        match D.compare m n with
        | Eq -> return ()
        | _ -> None)
    | Pi (name, dom1s, cod1s), Pi (_, dom2s, cod2s) -> (
        (* If two pi-types have the same dimension, equal domains, and equal codomains, they are equal and have the same type (an instantiation of the universe of that dimension at pi-types formed from the lower-dimensional domains and codomains). *)
        let k = CubeOf.dim dom1s in
        match D.compare (CubeOf.dim dom2s) k with
        | Eq ->
            Some
              (let open Monad.Ops (Err) in
               let open CubeOf.Monadic (Err) in
               let* () = miterM { it = (fun _ [ x; y ] -> equal_val ctx x y) } [ dom1s; dom2s ] in
               (* We create variables for all the domains, in order to equality-check all the codomains.  The codomain boundary types only use some of those variables, but it doesn't hurt to have the others around. *)
               let newargs, newnfs = dom_vars ctx dom1s in
               let (Any_ctx newctx) = Ctx.variables_vis ctx name newnfs in
               let open BindCube.Monadic (Err) in
               miterM
                 {
                   it =
                     (fun s [ cod1; cod2 ] ->
                       let sargs = CubeOf.subcube s newargs in
                       equal_val newctx (apply_binder_term cod1 sargs)
                         (apply_binder_term cod2 sargs));
                 }
                 [ cod1s; cod2s ])
        | Neq -> None)
    | _, _ -> None

  (* Check that the arguments of two entire application spines of equal functions are equal.  This is basically a left fold, but we make sure to iterate from left to right, and fail rather than raising an exception if the lists have different lengths.  As noted above, here we can go back to *assuming* that they have equal types, and thus passing off to the eta-expanding equality check.  *)
  and equal_apps : type any1 any2 a b. (a, b) Ctx.t -> any1 apps -> any2 apps -> unit ErrOpt.t =
   fun ctx apps1 apps2 ->
    let open Monad.Ops (ErrOpt) in
    (* Iterating from left to right is important because it ensures that at the point of checking equality for any pair of arguments, we know that they have the same type, since they are valid arguments of equal functions with all previous arguments equal.  Thus each case *starts* with its recursive call. *)
    match (apps1, apps2) with
    | Emp, Emp -> return ()
    | Arg (rest1, a1, i1), Arg (rest2, a2, i2) -> (
        let* () = equal_apps ctx rest1 rest2 in
        let To d1, To d2 = (deg_of_ins i1, deg_of_ins i2) in
        let* () = ErrOpt.of_opt (deg_equiv d1 d2) in
        match D.compare (CubeOf.dim a1) (CubeOf.dim a2) with
        | Eq ->
            let open CubeOf.Monadic (Err) in
            Some (miterM { it = (fun _ [ x; y ] -> (equal_nf ctx) x y) } [ a1; a2 ])
        (* If the dimensions don't match, it is a bug rather than a user error, since they are supposed to both be valid arguments of the same function, and any function has a unique dimension. *)
        | Neq ->
            fatal
              (Dimension_mismatch ("application in equality-check", CubeOf.dim a1, CubeOf.dim a2)))
    | Field (rest1, f1, _, i1), Field (rest2, f2, _, i2) -> (
        let* () = equal_apps ctx rest1 rest2 in
        let To d1, To d2 = (deg_of_ins i1, deg_of_ins i2) in
        let* () = ErrOpt.of_opt (deg_equiv d1 d2) in
        (* The 'plus' parts must automatically be equal if the fields are equal and well-typed. *)
        match Field.equal f1 f2 with
        | Eq -> Some (Ok ())
        | Neq -> Some (Error (Unequal.Fields (f1, f2))))
    | Inst (rest1, _, a1), Inst (rest2, _, a2) ->
        let* () = equal_apps ctx rest1 rest2 in
        equal_tyargs ctx a1 a2
    | _, _ -> None

  and equal_at_tel : type n a b ab c d.
      (c, d) Ctx.t ->
      (n, a) env ->
      kinetic value list ->
      kinetic value list ->
      (a, b, ab) Telescope.t ->
      (D.zero, n, n, kinetic value list) TubeOf.t ->
      unit Err.t =
   fun ctx env xs ys tys tyargs ->
    match (xs, ys, tys) with
    | [], [], Emp -> ok
    | x :: xs, y :: ys, Ext (_, ty, tys) ->
        let ety = eval_term env ty in
        (* Copied from check_tel; TODO: Factor it out *)
        let tyargtbl = Hashtbl.create 10 in
        let [ tyarg; tyargs ] =
          TubeOf.pmap
            {
              map =
                (fun fa [ tyargs ] ->
                  match tyargs with
                  | [] -> fatal (Anomaly "missing arguments in equal_at_tel")
                  | argtm :: argrest ->
                      let fa = sface_of_tface fa in
                      let argty =
                        inst
                          (eval_term (act_env env (op_of_sface fa)) ty)
                          (TubeOf.build D.zero
                             (D.zero_plus (dom_sface fa))
                             {
                               build =
                                 (fun fb ->
                                   Hashtbl.find tyargtbl
                                     (SFace_of (comp_sface fa (sface_of_tface fb))));
                             }) in
                      let argnorm = { tm = argtm; ty = argty } in
                      Hashtbl.add tyargtbl (SFace_of fa) argnorm;
                      [ argnorm; argrest ]);
            }
            [ tyargs ] (Cons (Cons Nil)) in
        let ity = inst ety tyarg in
        let* () = equal_at ctx x y ity in
        equal_at_tel ctx
          (Ext
             ( env,
               D.plus_zero (TubeOf.inst tyarg),
               Ok (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x)) ))
          xs ys tys tyargs
    | _ -> fatal (Anomaly "length mismatch in equal_at_tel")

  and equal_env : type a b n c d.
      (c, d) Ctx.t -> (n, b) env -> (n, b) env -> (a, b) termctx -> unit Err.t =
   fun ctx env1 env2 (Permute (_, envctx)) -> equal_ordered_env ctx env1 env2 envctx

  and equal_ordered_env : type a b n c d.
      (c, d) Ctx.t -> (n, b) env -> (n, b) env -> (a, b) ordered_termctx -> unit Err.t =
   fun ctx env1 env2 envctx ->
    (* Copied from readback_ordered_env *)
    match envctx with
    | Emp -> ok
    | Lock envctx -> equal_ordered_env ctx env1 env2 envctx
    | Ext (envctx, entry, _) -> (
        let open CubeOf.Monadic (Err) in
        let (Plus mk) = D.plus (dim_entry entry) in
        let (Looked_up { act = act1; op = Op (fc1, fd1); entry = xs1 }) =
          lookup_cube env1 mk Now (id_op (D.plus_out (dim_env env1) mk)) in
        let xs1 = act_cube { act = act1 } (CubeOf.subcube fc1 xs1) fd1 in
        let (Looked_up { act = act2; op = Op (fc2, fd2); entry = xs2 }) =
          lookup_cube env2 mk Now (id_op (D.plus_out (dim_env env2) mk)) in
        let xs2 = act_cube { act = act2 } (CubeOf.subcube fc2 xs2) fd2 in
        let env1' = remove_env env1 Now in
        let env2' = remove_env env2 Now in
        let* () = equal_ordered_env ctx env1' env2' envctx in
        match entry with
        | Vis { bindings; _ } | Invis bindings ->
            let xtytbl = Hashtbl.create 10 in
            let* _ =
              mmapM
                {
                  map =
                    (fun fab [ tm1; tm2 ] ->
                      let (SFace_of_plus (_, fb, fa)) = sface_of_plus mk fab in
                      let ty = (CubeOf.find bindings fa).ty in
                      let k = dom_sface fb in
                      let ty =
                        inst
                          (eval_term (act_env env1 (op_of_sface fb)) ty)
                          (TubeOf.build k (D.plus_zero k)
                             {
                               build =
                                 (fun fc ->
                                   Hashtbl.find xtytbl
                                     (SFace_of (comp_sface fb (sface_of_tface fc))));
                             }) in
                      Hashtbl.add xtytbl (SFace_of fb) { tm = tm1; ty };
                      equal_at ctx tm1 tm2 ty);
                }
                [ xs1; xs2 ] in
            return ())
end

let fallback f =
  match Mode.run ~env:`Rigid f with
  | Error err -> if GluedEval.read () then Mode.run ~env:`Full f else Error err
  | Ok x -> Ok x

let fallback_opt f =
  let res = Mode.run ~env:`Rigid f in
  match res with
  | None | Some (Error _) -> if GluedEval.read () then Mode.run ~env:`Full f else None
  | Some (Ok ()) -> Some (Ok ())

let equal_at ctx x y ty = fallback @@ fun () -> Equal.equal_at ctx x y ty
let equal_val ctx x y = fallback @@ fun () -> Equal.equal_val ctx x y
let equal_nf ctx x y = fallback @@ fun () -> Equal.equal_nf ctx x y
let equal_tyargs ctx a1 a2 = fallback_opt @@ fun () -> Equal.equal_tyargs ctx a1 a2
let equal_apps ctx a1 a2 = fallback_opt @@ fun () -> Equal.equal_apps ctx a1 a2
