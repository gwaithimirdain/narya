open Util
open Tlist
open Modal
open Reporter
open Printable
open Dim
open Term
open Value
open Tctx
open Domvars
open Norm
open Act
open Readback
module Err = Monad.Error (Unequal)
open Monad.Ops (Err)

let guard test err = if test then Ok () else Error err
let fail err = Error err

(* Whether one prekey action is a postwhiskering of another: there is a modality that, composed onto the vertical target of pre2, yields pre1.  Since a prekey acts on a value (which lies behind the appropriate modality) by extending its key with factoring, the extra target modality is absorbed, so a postwhiskering acts the same way.  In particular an identity 2-cell is a postwhiskering of an identity (id2), so the two are prekey-equal. *)
let prekey_le : type mode m1 n1 c1 m2 n2 c2.
    (mode, m1, n1, c1) Modalcell.t -> (mode, m2, n2, c2) Modalcell.t -> bool =
 fun pre1 pre2 ->
  match Modality.factor (Modalcell.vsrc pre1) (Modalcell.vsrc pre2) with
  | None -> false
  | Some (Factor (m, _)) -> (
      let (Wrap p) = Modalcell.postwhisker_wrapped m pre2 in
      match Modalcell.compare p pre1 with
      | Eq -> true
      | Neq -> false)

(* Two prekey actions are considered equal if they compare equal or if either is a postwhiskering of the other. *)
let prekey_equal : type mode m1 n1 c1 m2 n2 c2.
    (mode, m1, n1, c1) Modalcell.t -> (mode, m2, n2, c2) Modalcell.t -> bool =
 fun pre1 pre2 ->
  (match Modalcell.compare pre1 pre2 with
    | Eq -> true
    | Neq -> false)
  || prekey_le pre1 pre2
  || prekey_le pre2 pre1

let if_known (test : 'a Err.t option) err =
  match test with
  | None -> Error (err ())
  | Some x -> x

let ok = Ok ()

(* If an application spine crosses no modal field projection (every field has the identity left adjoint), then its head lives at the ambient mode; this returns a witness of that mode equality, or None if the spine is modal. *)
let rec nonmodal_apps : type hmode mode any. (hmode, mode, any) apps -> (hmode, mode) Eq.t option =
  function
  | Emp -> Some Eq
  | Arg (rest, _, _, _) -> nonmodal_apps rest
  | Inst (rest, _, _) -> nonmodal_apps rest
  | Field (rest, filter, _, _, _) -> (
      match Modality.compare_id (Modality.filter_modality filter) with
      | Eq -> nonmodal_apps rest
      | Neq -> None)

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

(* Compare two normal forms that are *assumed* to have the same type, or at least that the type of the first is a subtype of the type of the second. *)
let rec equal_nf : type mode a b. (mode, a, b) Ctx.t -> mode normal -> mode normal -> unit Err.t =
 fun n x y ->
  (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  We check them at the type of the *second* argument, since this is also called as a subroutine of subtype checking, in which case the subtype comes first and then the supertype. *)
  equal_at n x.tm y.tm y.ty

(* At a type with an eta-rule, two neutrals with equal spines are nevertheless equal, and checking this first can avoid an eta-expansion.  This matters especially with glued evaluation, where parallel derivations produce equal retained spines that are not physically shared, and where eta-expanding compares (and hence unfolds and re-evaluates) their realizations instead.  A spine mismatch is inconclusive at an eta type, so callers fall back to eta-expanding. *)
and equal_at_eta_spines : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) value -> (mode, kinetic) value -> unit option =
 fun ctx x y ->
  match (x, y) with
  | Neu _, Neu _ -> (
      match equal_neu ctx x y with
      | Ok () -> Some ()
      | Error _ -> None)
  | _ -> None

(* Compare two values at a type, which they are both assumed to belong to.  We do eta-expansion here if the type is one with an eta-rule, like a pi-type or a record type.  We also deal with the case of terms that don't synthesize, such as structs even in codatatypes without eta, and constructors in datatypes. *)
and equal_at : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    unit Err.t =
 fun ctx x y ty ->
  (* Physically equal values are definitionally equal, and physical sharing is common (cached constants, shared let-bindings, shared forced values), so we short-circuit on it before any structural work. *)
  if x == y then ok
  else
    (* The type must be fully instantiated. *)
    match view_type ty "equal_at" with
    (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
    | Canonical (_, Pi { x = name; filter; doms; cods }, ins, tyargs) -> (
        match equal_at_eta_spines ctx x y with
        | Some () -> ok
        | None ->
            let modality = Modality.filter_modality filter in
            let Eq = eq_of_ins_zero ins in
            let newargs, newnfs = dom_vars ctx modality doms in
            let (Any_ctx newctx) =
              Ctx.variables_vis ctx (Modality.filter_idempotent filter) name newnfs in
            let output = tyof_app cods tyargs filter newargs in
            (* If both terms have the given pi-type, then when applied to variables of the domains, they will both have the computed output-type, so we can recurse back to eta-expanding equality at that type. *)
            equal_at newctx (apply_term x filter newargs) (apply_term y filter newargs) output)
    (* Codatatypes (without eta) don't need to be dealt with here, even though structs can't be compared synthesizingly, since codatatypes aren't actually inhabited by (kinetic) structs, only neutral terms that are equal to potential structs.  In the case of record types with eta, if there is a nonidentity insertion outside, then the type isn't actually a record type, *but* it still has an eta-rule since it is *isomorphic* to a record type!  Thus, instead of checking whether the insertion is the identity, we apply its inverse permutation to the terms being compared.  And because we pass off to 'field' and 'tyof_field', we don't need to make explicit use of any of the other data here. *)
    | Canonical
        (type hmode mn m n)
        ((_, Codata (type c a et) ({ eta; fields; _ } : (mode, m, n, c, a, et) codata_args), ins, _) :
          hmode head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t) -> (
        match eta with
        | Eta -> (
            match equal_at_eta_spines ctx x y with
            | Some () -> ok
            | None ->
                let (Perm_to p) = perm_of_ins ins in
                let pinv = deg_of_perm (perm_inv p) in
                let x, y, ty =
                  let idc = Modalcell.id2 (Ctx.mode ctx) in
                  (act_value x pinv idc, act_value y pinv idc, gact_ty None ty pinv idc) in
                (* Now we take the projections and compare them at appropriate types.  It suffices to use the fields of x when computing the types of the fields, since we proceed to check the fields for equality *in order* and thus by the time we are checking equality of any particular field of x and y, the previous fields of x and y are already known to be equal, and the type of the current field can only depend on these.  (This latter is a semantic constraint on the kinds of generalized records that can sensibly admit eta-conversion.)  In addition, records with eta cannot have higher fields, so as field insertion it suffices to use ins_zero on the substitution dimension. *)
                let fldins = ins_zero (cod_left_ins ins) in
                BwdM.miterM
                  (fun [
                         CodatafieldAbwd.Entry
                           (type i)
                           ((fld, Lower (adj, _, _)) :
                             i Field.t * (i, mode * a * n * has_eta) Codatafield.t);
                       ] ->
                    (* For a modal field, both terms are keyed by the adjunction unit to put them into a context where the modal field can be projected, and the projections are compared in the context locked by the right adjoint.  For ordinary fields the unit is the identity and the lock is trivial. *)
                    let (Adjunction { left; right; unit; _ }) = adj in
                    (* A modal field whose (left adjoint) modality is nonparametric disappears at a dimension it filters nontrivially, so it plays no role in checikng equality. *)
                    let m = cod_left_ins ins in
                    let (Has_filter left_filter) = Modality.filter left m in
                    match Modality.filter_is_trivial m left_filter with
                    | None -> return ()
                    | Some Eq ->
                        let xu = act_value x (id_deg D.zero) unit in
                        let yu = act_value y (id_deg D.zero) unit in
                        let tyu = gact_ty None ty (id_deg D.zero) unit in
                        let (Locked (_, lctx)) = Ctx.lock ctx right in
                        equal_at lctx (field_term left xu fld fldins)
                          (field_term left yu fld fldins)
                          (tyof_field left (Ok xu) tyu fld ~shuf:Trivial fldins))
                  [ fields ])
        (* At a codatatype without eta, there are no kinetic structs, only comatches, and those are not compared componentwise, only as neutrals, since they are generative. *)
        | Noeta -> equal_val ctx x y)
    (* At a higher-dimensional version of a discrete datatype, any two terms are equal.  Note that we do not check here whether discreteness is on: that affects datatypes when they are *defined*, not when they are used. *)
    | Canonical (_, Data { dim; discrete = `Yes; _ }, _, _) when is_pos dim -> return ()
    (* At an ordinary datatype, two constructors are equal if they are instances of the same constructor, with the same dimension and arguments.  We handle these cases here because we can use the datatype information to give types to the arguments of the constructor. *)
    | Canonical (_, Data { constrs; _ }, ins, tyargs) ->
        let Eq = eq_of_ins_zero ins in
        (* With glued evaluation, terms at a datatype may be glued neutrals whose values unfold to constructors.  We compare the terms as given, and only if that is inconclusive (a neutral spine mismatch, or a shape mismatch) do we unfold with view_term and retry.  Since view_term unfolds Realized glued values all the way down, a second view is the physical identity and the retry recursion terminates. *)
        let rec equal_at_data (x : (mode, kinetic) value) (y : (mode, kinetic) value) : unit Err.t =
          match (x, y) with
          | Constr (xconstr, xn, xargs), Constr (yconstr, yn, yargs) -> (
              let (Dataconstr { env; args = argtys; indices = _ }) =
                match Abwd.find_opt xconstr constrs with
                | Some x -> x
                | None -> fatal (Anomaly "constr not found in equality-check") in
              let* () = guard (xconstr = yconstr) (Unequal.Constrs (xconstr, yconstr)) in
              match (D.compare xn yn, D.compare xn (TubeOf.inst tyargs)) with
              | Neq, _ -> fatal (Dimension_mismatch ("equality of constrs", xn, yn))
              | _, Neq -> fatal (Dimension_mismatch ("equality of constrs", xn, TubeOf.inst tyargs))
              | Eq, Eq ->
                  let lgth = Telescope.length argtys in
                  let xargs =
                    Vec.of_list_length lgth xargs
                    <|> Anomaly "wrong number of constructor arguments in readback_at" in
                  let yargs =
                    Vec.of_list_length lgth yargs
                    <|> Anomaly "wrong number of constructor arguments in readback_at" in
                  let (Conses (cs, bs)) = Tlist.conses lgth in
                  (* The instantiation must be at other instances of the same constructor; we take its arguments as in 'check'. *)
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
                                       <|> Anomaly "inst arg wrong num args in readback at datatype"
                                     in
                                     CubeOf.Heter.hft_of_vec cs ys
                                   else
                                     fatal (Anomaly "inst arg wrong constr in equality at datatype")
                               | _ -> fatal (Anomaly "inst arg not constr in equality at datatype"));
                         }
                         [ tyargs ] bs in
                  (* It suffices to compare the top-dimensional faces of the cubes; the others are only there for evaluating case trees.  It would be nice to do this recursion directly on the Bwds, but equal_at_tel is expressed much more cleanly as an operation on lists. *)
                  equal_at_tel ctx env xargs yargs argtys tyarg_args)
          | Neu _, Neu _ -> (
              (* Two neutrals are first compared as spines; a mismatch is inconclusive if either side unfolds, in which case we retry (once) on the unfoldings, which may now be constructors. *)
              match equal_neu ctx x y with
              | Ok () -> ok
              | Error err ->
                  let vx = view_term x in
                  let vy = view_term y in
                  if vx == x && vy == y then Error err else equal_at_data vx vy)
          | _ -> (
              let vx = view_term x in
              let vy = view_term y in
              if vx != x || vy != y then equal_at_data vx vy
              else
                match (x, y) with
                | Constr _, _ | _, Constr _ ->
                    fail
                      (Unequal.Terms (PNormal (ctx, { tm = x; ty }), PNormal (ctx, { tm = y; ty })))
                | _ -> equal_val ctx x y) in
        equal_at_data x y
    (* If the type is not one that has an eta-rule, then we pass off to a synthesizing equality-check, forgetting about our assumption that the two terms had the same type.  This is the equality-checking analogue of the conversion rule for checking a synthesizing term, but since equality requires no evidence we don't have to actually synthesize a type at which they are equal or verify that it equals the type we assumed them to have. *)
    | _ -> equal_val ctx x y

(* "Synthesizing" equality check of two values, now *not* assumed a priori to have the same type.  If this function concludes that they are equal, then the equality of their types is part of that conclusion. *)
and equal_val : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) value -> (mode, kinetic) value -> unit Err.t =
 fun ctx x y ->
  if x == y then ok
  else
    match (x, y) with
    | Neu _, Neu _ -> (
        (* Two neutrals are first compared rigidly as spines.  With glued evaluation, a spine mismatch is inconclusive if either side unfolds (its stored value is Realized): in that case we retry on the unfoldings.  Since view_term unfolds Realized glued values all the way down, a second view is the physical identity, so there is at most one retry per node and subterms that match as spines are never unfolded. *)
        match equal_neu ctx x y with
        | Ok () -> ok
        | Error err ->
            let vx = view_term x in
            let vy = view_term y in
            if vx == x && vy == y then Error err else equal_val ctx vx vy)
    | Lam _, _ | _, Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing equality-check")
    | Struct _, _ | _, Struct _ ->
        fatal (Anomaly "unexpected struct in synthesizing equality-check")
    | Constr _, _ | _, Constr _ ->
        fatal (Anomaly "unexpected constr in synthesizing equality-check")

(* Rigid spine comparison of two neutrals: heads and applications, with no unfolding at this level (though the arguments are compared with the full equality including local unfolding). *)
and equal_neu : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) value -> (mode, kinetic) value -> unit Err.t =
 fun ctx x y ->
  match (x, y) with
  | ( Neu { head = head1; args = apps1; value = _; ty = _ },
      Neu { head = head2; args = apps2; value = _; ty = _ } ) -> (
      (* To check two neutral applications are equal, with their types, we check if the functions are equal, including their types and hence also their domains and codomains (and also they have the same insertion applied outside).  We don't need to check that the types agree; this procedure concludes equality of types rather than assumes it. *)
      match (nonmodal_apps apps1, nonmodal_apps apps2) with
      (* If neither spine crosses a modal field projection, the heads are at the ambient mode and we can compare them first (as we always did before modal fields), which gives more precise "unequal heads" error messages. *)
      | Some Eq, Some Eq -> (
          match equal_head ctx head1 head2 with
          | Some (Error err) -> Error (Unequal.Heads err)
          | None ->
              let h1, h2 = (readback_head ctx head1, readback_head ctx head2) in
              Error (Unequal.Heads (Terms (PTerm (ctx, h1), PTerm (ctx, h2))))
          | Some (Ok ()) -> (
              match equal_apps ctx apps1 apps2 with
              | None -> Error (Unequal.Terms (PVal (ctx, x), PVal (ctx, y)))
              | Some x -> x))
      (* Otherwise, the heads live at the mode at the head end of the spine, so the head comparison happens at the bottom of the spine recursion, in the context locked by the modal field projections crossed on the way. *)
      | _ -> (
          match equal_apps ctx apps1 apps2 ~heads:(head1, head2) with
          | None -> Error (Unequal.Terms (PVal (ctx, x), PVal (ctx, y)))
          | Some x -> x))
  | Lam _, _ | _, Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing equality-check")
  | Struct _, _ | _, Struct _ -> fatal (Anomaly "unexpected struct in synthesizing equality-check")
  | Constr _, _ | _, Constr _ -> fatal (Anomaly "unexpected constr in synthesizing equality-check")

and equal_tyargs : type mode n1 k1 nk1 n2 k2 nk2 a b.
    (mode, a, b) Ctx.t ->
    (n1, k1, nk1, mode normal) TubeOf.t ->
    (n2, k2, nk2, mode normal) TubeOf.t ->
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
and equal_head : type mode a b. (mode, a, b) Ctx.t -> mode head -> mode head -> unit ErrOpt.t =
 fun ctx x y ->
  let open Monad.Ops (ErrOpt) in
  match (x, y) with
  | Var { level = l1; deg = d1; key = k1 }, Var { level = l2; deg = d2; key = k2 } ->
      (* Two equal variables with the same degeneracy and key applied are equal, including their types because that variable has only one type. *)
      if l1 = l2 then
        if Option.is_some (deg_equiv d1 d2) then
          match Modalcell.compare k1 k2 with
          | Eq -> return ()
          | Neq -> None
        else None
      else
        Some
          (Error (Variables (PTerm (ctx, readback_head ctx x), PTerm (ctx, readback_head ctx y))))
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
  | UU (_, m), UU (_, n) -> (
      (* Two universes are equal precisely when they have the same dimension, in which case they also automatically have the same type (a standard instantiation of a (higher) universe of that same dimension).  We don't need to compare the modes because the type of this function guarantees they are at the same mode. *)
      match D.compare m n with
      | Eq -> return ()
      | _ -> None)
  | ( Pi
        (type xdom xmodality xk n)
        ({ x = name; filter = filter1; doms = dom1s; cods = cod1s } :
          (xdom, xmodality, mode, xk, n) pi_args),
      Pi { x = _; filter = filter2; doms = dom2s; cods = cod2s } ) -> (
      (* If two pi-types have the same dimension, equal domains, and equal codomains, they are equal and have the same type (an instantiation of the universe of that dimension at pi-types formed from the lower-dimensional domains and codomains). *)
      let modality1, modality2 =
        (Modality.filter_modality filter1, Modality.filter_modality filter2) in
      let n = BindCube.dim cod1s in
      match (D.compare (BindCube.dim cod2s) n, Modality.compare modality1 modality2) with
      | Eq, Eq ->
          let Eq = Modality.filter_uniq filter1 filter2 in
          let (Locked (_, lctx)) = Ctx.lock ctx modality1 in
          Some
            (let open Monad.Ops (Err) in
             let open CubeOf.Monadic (Err) in
             let* () = miterM { it = (fun _ [ x; y ] -> equal_val lctx x y) } [ dom1s; dom2s ] in
             (* We create variables for all the domains, in order to equality-check all the codomains.  The codomain boundary types only use some of those variables, but it doesn't hurt to have the others around. *)
             let newargs, newnfs = dom_vars ctx modality1 dom1s in
             let (Any_ctx newctx) =
               Ctx.variables_vis ctx (Modality.filter_idempotent filter1) name newnfs in
             (* We compare the two cubes of codomains with the binary iterator miter2M, which recurses directly on the two trees.  We cannot use the generic n-ary miterM [ cod1s; cod2s ] here: iterating two cubes whose element family (BindFam) is a multi-parameter GADT via the heterogeneous Tlist machinery sends type inference into a catastrophic blowup (~15s and 14GB to compile this one expression). *)
             let open BindCube.Monadic (Err) in
             miter2M
               {
                 it2 =
                   (fun s (BindFam cod1) (BindFam cod2) ->
                     let (Filter_sface (fb, kfilter)) = Modality.filter_sface filter1 s in
                     let sargs = CubeOf.subcube fb newargs in
                     equal_val newctx
                       (apply_binder_term cod1 kfilter sargs)
                       (apply_binder_term cod2 kfilter sargs));
               }
               cod1s cod2s)
      | Neq, _ | _, Neq -> None)
  | _, _ -> None

(* Check that the arguments of two entire application spines of equal functions are equal.  This is basically a left fold, but we make sure to iterate from left to right, and fail rather than raising an exception if the lists have different lengths.  As noted above, here we can go back to *assuming* that they have equal types, and thus passing off to the eta-expanding equality check.  If heads are supplied, they are compared at the bottom of the recursion, where the context has been locked by the left adjoints of any modal field projections crossed on the way in, so that it lives at the heads' mode. *)
and equal_apps : type h1 h2 mode any1 any2 a b.
    (mode, a, b) Ctx.t ->
    ?heads:h1 head * h2 head ->
    (h1, mode, any1) apps ->
    (h2, mode, any2) apps ->
    unit ErrOpt.t =
 fun ctx ?heads apps1 apps2 ->
  let open Monad.Ops (ErrOpt) in
  (* Iterating from left to right is important because it ensures that at the point of checking equality for any pair of arguments, we know that they have the same type, since they are valid arguments of equal functions with all previous arguments equal.  Thus each case *starts* with its recursive call. *)
  match (apps1, apps2) with
  | Emp, Emp -> (
      match heads with
      | None -> return ()
      | Some (head1, head2) -> (
          match equal_head ctx head1 head2 with
          | Some (Ok ()) -> return ()
          | Some (Error err) -> Some (Error (Unequal.Heads err))
          | None ->
              let t1, t2 = (readback_head ctx head1, readback_head ctx head2) in
              Some (Error (Unequal.Heads (Terms (PTerm (ctx, t1), PTerm (ctx, t2)))))))
  | Arg (rest1, filter1, a1, i1), Arg (rest2, filter2, a2, i2) -> (
      let modality1 = Modality.filter_modality filter1 in
      let modality2 = Modality.filter_modality filter2 in
      match Modality.compare modality1 modality2 with
      | Neq -> None
      | Eq -> (
          let* () = equal_apps ctx rest1 rest2 ?heads in
          let To d1, To d2 = (deg_of_ins i1, deg_of_ins i2) in
          let* () = ErrOpt.of_opt (deg_equiv d1 d2) in
          let (Locked (_, lctx)) = Ctx.lock ctx modality1 in
          match D.compare (CubeOf.dim a1) (CubeOf.dim a2) with
          | Eq ->
              let open CubeOf.Monadic (Err) in
              Some (miterM { it = (fun _ [ x; y ] -> equal_nf lctx x y) } [ a1; a2 ])
          (* If the dimensions don't match, it is a bug rather than a user error, since they are supposed to both be valid arguments of the same function, and any function has a unique dimension. *)
          | Neq ->
              fatal
                (Dimension_mismatch ("application in equality-check", CubeOf.dim a1, CubeOf.dim a2))
          ))
  | Field (rest1, filter1, f1, _, i1), Field (rest2, filter2, f2, _, i2) -> (
      (* The spines inside a modal field projection live behind a lock by the left adjoint, so we compare them in the locked context.  Comparing the field modalities suffices; the filters are then determined by the (equal) result dimensions of the two spines. *)
      let fm1 = Modality.filter_modality filter1 in
      let fm2 = Modality.filter_modality filter2 in
      match Modality.compare fm1 fm2 with
      | Neq -> None
      | Eq -> (
          let (Locked (_, lctx)) = Ctx.lock ctx fm1 in
          let* () = equal_apps lctx rest1 rest2 ?heads in
          let To d1, To d2 = (deg_of_ins i1, deg_of_ins i2) in
          let* () = ErrOpt.of_opt (deg_equiv d1 d2) in
          (* The 'plus' parts must automatically be equal if the fields are equal and well-typed. *)
          match Field.equal f1 f2 with
          | Eq -> Some (Ok ())
          | Neq -> Some (Error (Unequal.Fields (f1, f2)))))
  | Inst (rest1, _, a1), Inst (rest2, _, a2) ->
      let* () = equal_apps ctx rest1 rest2 ?heads in
      equal_tyargs ctx a1 a2
  | _, _ -> None

and equal_at_tel : type mode n a b ab c d.
    (mode, c, d) Ctx.t ->
    (mode, n, a) env ->
    ((n, mode, kinetic) modal_value_cube, b) Vec.t ->
    ((n, mode, kinetic) modal_value_cube, b) Vec.t ->
    (mode, a, b, ab) Telescope.t ->
    ((D.zero, n, n, (mode, kinetic) modal_value) TubeOf.t, b) Vec.t ->
    unit Err.t =
 fun ctx env xs ys tys tyargs ->
  match (xs, ys, tys, tyargs) with
  | [], [], Emp, [] -> ok
  | ( Modal
        (type xdom xmodality xk)
        ((xfilter, x) :
          (xdom, xmodality, mode, xk, n) Modality.filter_dim * (xk, (xdom, kinetic) value) CubeOf.t)
      :: xs,
      Modal
        (type ydom ymodality yk)
        ((yfilter, y) :
          (ydom, ymodality, mode, yk, n) Modality.filter_dim * (yk, (ydom, kinetic) value) CubeOf.t)
      :: ys,
      Ext (_, Modal (tymodality, aplus, ty), tys),
      tyargs :: tyargs_rest ) -> (
      let xmodality = Modality.filter_modality xfilter in
      let ymodality = Modality.filter_modality yfilter in
      match (Modality.compare xmodality tymodality, Modality.compare ymodality tymodality) with
      | Eq, Eq ->
          let Eq = Modality.filter_uniq xfilter yfilter in
          let (Locked (_, lctx)) = Ctx.lock ctx tymodality in
          let lenv = key_id_env env aplus in
          let x = CubeOf.find_top x in
          let y = CubeOf.find_top y in
          let ety = eval_term lenv ty in
          let n = dim_env env in
          let k = Modality.filtered n xfilter in
          let tyargtbl = Hashtbl.create 10 in
          let tyarg =
            TubeOf.build D.zero (D.zero_plus k)
              {
                build =
                  (fun fa ->
                    (* The value associated to some face of k in the cube of arguments is derived from the corresponding argument of the n-dimensional constructor associated to the corresponding face of n lifted along the filter.  This makes sense because when a constructor is evaluated, the modally filtered arguments are degenerated to obtain values for the boundary constructors, and the face and degeneracy cancel out. *)
                    let (Pface_filter (_, fb)) = Modality.pface_filter n fa xfilter in
                    let (Modal (argmod, argtm)) = TubeOf.find tyargs fb in
                    match Modality.compare argmod xmodality with
                    | Neq ->
                        fatal (Modality_mismatch (`Internal, "equal_at_tel", argmod, tymodality))
                    | Eq ->
                        let fa = sface_of_tface fa in
                        let fb = sface_of_tface fb in
                        let argty : (xdom, kinetic) value =
                          inst
                            (eval_term
                               (act_env lenv
                                  (opt_op_of_opt_sface
                                     (comp_opt_sface
                                        (Modality.sface_of_filter n xfilter)
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
                        let argnorm : xdom normal = { tm = argtm; ty = argty } in
                        Hashtbl.add tyargtbl (SFace_of fb) argnorm;
                        argnorm);
              } in
          let ity = inst ety tyarg in
          let* () = equal_at lctx x y ity in
          equal_at_tel ctx
            (Ext
               {
                 env;
                 plus = D.plus_zero (TubeOf.inst tyarg);
                 filter = xfilter;
                 filtered = Modality.filter_zero xmodality;
                 values = `Ok (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x));
               })
            xs ys tys tyargs_rest
      | Neq, _ -> fatal (Modality_mismatch (`Internal, "equal_at_tel", xmodality, tymodality))
      | _, Neq -> fatal (Modality_mismatch (`Internal, "equal_at_tel", ymodality, tymodality)))

and equal_env : type mode a b n c d.
    (mode, c, d) Ctx.t -> (mode, n, b) env -> (mode, n, b) env -> (mode, a, b) termctx -> unit Err.t
    =
 fun ctx env1 env2 (Permute (_, envctx)) -> equal_ordered_env ctx env1 env2 envctx

and equal_ordered_env : type mode a b n c d.
    (mode, c, d) Ctx.t ->
    (mode, n, b) env ->
    (mode, n, b) env ->
    (mode, a, b) ordered_termctx ->
    unit Err.t =
 fun ctx env1 env2 envctx ->
  (* Copied from readback_ordered_env *)
  match envctx with
  | Emp _ -> ok
  (* A weakening entry contributes nothing to the environment, so we skip it. *)
  | Weaken (envctx, _) -> equal_ordered_env ctx env1 env2 envctx
  | Ext (envctx, entry, _) -> (
      let open CubeOf.Monadic (Err) in
      match entry with
      | Vis { plus_lock = dplus; bindings; _ } | Invis { plus_lock = dplus; bindings; _ } ->
          let modality = plus_lock_modality dplus in
          let n = dim_env env1 in
          let (Has_filter filter) = Modality.filter modality n in
          let m = Modality.filtered n filter in
          let k = dim_entry entry in
          let (Plus m_k) = D.plus k in
          let mk = D.plus_out m m_k in
          (* 1 *)
          let aenv1 = act_env env1 (opt_op_of_opt_sface (Modality.sface_of_filter n filter)) in
          let (Looked_up { act = act1; op = op1; entry = xs1; pre = pre1 }) =
            lookup_cube aenv1 m_k modality modality Now (id_opt_op mk) in
          let (Op (fc1, fd1)) =
            op_of_opt op1 <|> Anomaly "unexpected missing endpoint 1 in equal_ordered_env" in
          let xs1 = act_cube { act = act1 } (CubeOf.subcube fc1 xs1) fd1 pre1 in
          (* 2 *)
          let aenv2 = act_env env2 (opt_op_of_opt_sface (Modality.sface_of_filter n filter)) in
          let (Looked_up { act = act2; op = op2; entry = xs2; pre = pre2 }) =
            lookup_cube aenv2 m_k modality modality Now (id_opt_op mk) in
          let (Op (fc2, fd2)) =
            op_of_opt op2 <|> Anomaly "unexpected missing endpoint 1 in equal_ordered_env" in
          let xs2 = act_cube { act = act2 } (CubeOf.subcube fc2 xs2) fd2 pre2 in
          (* compare *)
          let (Locked (_, lctx)) = Ctx.lock ctx modality in
          let lenv = key_id_env aenv1 dplus in
          let env1' = remove_top env1 in
          let env2' = remove_top env2 in
          let* () = equal_ordered_env ctx env1' env2' envctx in
          let xtytbl = Hashtbl.create 10 in
          let* _ =
            mmapM
              {
                map =
                  (fun fab [ tm1; tm2 ] ->
                    let (SFace_of_plus (_, fb, fa)) = sface_of_plus m_k fab in
                    let ty = (CubeOf.find bindings fa).ty in
                    let ety = eval_term (act_env lenv (opt_op_of_sface fb)) ty in
                    let ty =
                      inst ety
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fb))
                           {
                             build =
                               (fun fc ->
                                 Hashtbl.find xtytbl (SFace_of (comp_sface fb (sface_of_tface fc))));
                           }) in
                    Hashtbl.add xtytbl (SFace_of fb) { tm = tm1; ty };
                    equal_at lctx tm1 tm2 ty);
              }
              [ xs1; xs2 ] in
          return ())
  | Lock _ -> (
      let (Ordered_remove_locks (envctx, locks, no_locks)) = Termctx.ordered_remove_locks envctx in
      let (Restrict_keys (env1, extra1, _, keys1, pre1)) = restrict_keys_plus_lock env1 locks in
      let (Restrict_keys (env2, extra2, _, keys2, pre2)) = restrict_keys_plus_lock env2 locks in
      (* Since we removed a maximal run of locks, and a key can only span locks, the split can never land in the middle of a key here, so there is nothing extra. *)
      match (extra1, extra2, no_locks) with
      | Plus_lock (Suc _, _), _, _ | _, Plus_lock (Suc _, _), _ -> .
      | Plus_lock (Zero _, Zero), Plus_lock (Zero _, Zero), _ -> (
          match Modalcell.compare keys1 keys2 with
          | Neq -> Error (Unequal.Cells (keys1, keys2))
          | Eq ->
              let* () = guard (prekey_equal pre1 pre2) (Unequal.Cells (pre1, pre2)) in
              (* The (equal) prekey actions mediate between a context locked by their vertical source and the actual ambient context, locked by their vertical target.  So we remove the prekey's target from the context and re-lock with its source (both no-ops when there was no prekey) before removing the target of the composite key cell as usual. *)
              let (Remove_lock (ctx, _)) = Ctx.remove_lock ctx (Modalcell.vtgt pre1) in
              let (Locked (_, ctx)) = Ctx.lock ctx (Modalcell.vsrc pre1) in
              let (Remove_lock (ctx, _)) = Ctx.remove_lock ctx (Modalcell.vtgt keys1) in
              equal_ordered_env ctx env1 env2 envctx))
