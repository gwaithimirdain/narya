open Util
open Modal
open Reporter
open Printable
open Dim
open Term
open Value
open Env
open Tctx
open Domvars
open Norm
open Act
open Readback

(* An equality check has three possible outcomes: the values are equal, they are unequal, or they are stuck because their comparison depends on unsolved unification metavariables, so that they might become equal or unequal once one of those metavariables is solved.  In the latter two cases we record the mismatch that was found, to report if the values are never found to be equal; when stuck, we also record the metavariables that it is blocked on.  This blocker list is not necessarily complete: other metavariables appearing in the values might also unblock the comparison when solved. *)
type failure = Unequal of Unequal.t | Stuck of Unequal.t * blocker list

module Err = Monad.Error (struct
  type t = failure
end)

open Monad.Ops (Err)

let guard test err = if test then Ok () else Error (Unequal err)
let fail err = Error (Unequal err)

(* Modify the mismatch recorded in a failure, preserving whether it is stuck. *)
let map_why (f : Unequal.t -> Unequal.t) : failure -> failure = function
  | Unequal why -> Unequal (f why)
  | Stuck (why, blockers) -> Stuck (f why, blockers)

(* Run a short-circuiting iteration in the equality error monad.  The body is given a [check] function to apply to the [unit Err.t] result of comparing each pair of sub-objects; the first [Error] breaks out of the iteration (via a local exception) and becomes the overall result.  This replaces what used to be a traversal in the Err monad. *)
let short_circuit_err (body : (unit Err.t -> unit) -> unit) : unit Err.t =
  let exception Stop of failure in
  try
    body (function
      | Ok () -> ()
      | Error e -> raise_notrace (Stop e));
    Ok ()
  with Stop e -> Error e

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

(* If an application spine crosses no modal field projection (every field has the identity left adjoint), then its head lives at the ambient mode; this returns a witness of that mode equality, or None if the spine is modal. *)
let rec nonmodal_apps : type hmode mode any.
    (hmode, mode, any, live) apps -> (hmode, mode) Eq.t option = function
  | Emp -> Some Eq
  | Snoc (rest, Arg _) -> nonmodal_apps rest
  | Snoc (rest, Inst _) -> nonmodal_apps rest
  | Snoc (rest, Field (filter, _, _, _)) -> (
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

(* Eta-expanding equality checks.  In all functions, the integer is the current De Bruijn level, i.e. the length of the current context (we don't need any other information about the context). *)

(* Before comparing two values structurally, we try to solve a unification metavariable on either side with the other side.  The solver is defined in the downstream module Unify, since it needs readback, so we make it a forward reference set there.  It is passed the type at which the values are being compared, if known; otherwise it must check that the types agree.  If it solved a metavariable directly the values are now equal, while if it expanded one then it has also compared the result.  Otherwise, it may have found that the metavariable can't be solved to make them equal, however any other metavariables are solved, in which case a comparison that is stuck means they are unequal. *)
type attempt = Not_solved | Solved of unit Err.t | Impossible

type solver = {
  solve :
    'mode 'a 'b.
    ('mode, 'a, 'b) Ctx.t ->
    ('mode, kinetic) value ->
    ('mode, kinetic) value ->
    ('mode, kinetic) value option ->
    attempt;
}

let solver : solver ref = ref { solve = (fun _ _ _ _ -> Not_solved) }

(* A comparison of two neutral spines with the same head may fail and then succeed by unfolding them, so it shouldn't solve any metavariables while it might be abandoned, since those solutions may not be justified by the final comparison.  For example, if g ignores its arguments, then g ?v b1 and g a1 b2 are equal, and that says nothing about ?v.  Thus we first compare spines "flexibly", without solving anything. *)
let flexible = ref false

let flexibly (f : unit -> 'a) : 'a =
  if !flexible || not (Global.unsolved_unifs ()) then f ()
  else (
    flexible := true;
    Fun.protect ~finally:(fun () -> flexible := false) f)

(* Try to solve a metavariable in comparing two values; if that doesn't apply, continue with the given comparison. *)
let with_solver ctx x y ty (compare : unit -> unit Err.t) : unit Err.t =
  match if !flexible then Not_solved else !solver.solve ctx x y ty with
  | Solved result -> result
  | Not_solved -> compare ()
  | Impossible -> (
      match compare () with
      | Error (Stuck (why, _)) -> Error (Unequal why)
      | result -> result)

(* Whether an equality between neutrals forces their spines to be equal, even after any metavariables in them are solved.  This is so if the neutral is permanently stuck, because it is a variable, an axiom, or a case tree stuck on something other than a metavariable, or if it is a canonical type, since these are generative.  It is not so if it is stuck on a metavariable, or if its head is a metavariable, since that metavariable could turn out to ignore some of its arguments. *)
let forces_spine : type mode s. (mode, s) value -> bool = function
  | Neu { head = Live (Meta _); _ } -> false
  | Neu { head = Live _; value; _ } -> (
      match View.force_eval value with
      | Unrealized | Val (Canonical _) -> true
      | Realize _ | Blocked _ | Val _ -> false)
  | _ -> false

(* Add blockers to a list, omitting duplicates. *)
let union_blockers (bs1 : blocker list) (bs2 : blocker list) : blocker list =
  List.fold_left
    (fun acc (Blocker (m, _) as b) ->
      if
        List.exists
          (fun (Blocker (m', _)) ->
            match Meta.compare m m' with
            | Eq -> true
            | Neq -> false)
          acc
      then acc
      else acc @ [ b ])
    bs1 bs2

(* The unification metavariables that a neutral is blocked on, so that solving one of them might change the result of comparing it.  These are the metavariable that its value is blocked on, which includes that of an unsolved unification metavariable head, together with any that its arguments are blocked on, since solving those might make the spine of a metavariable a renaming.  A neutral that is permanently stuck has no blockers. *)
let blockers_of : type mode s. (mode, s) value -> blocker list =
 fun x ->
  let rec arg_blockers : type hmode mode any. (hmode, mode, any, live) apps -> blocker list =
    function
    | Emp -> []
    | Snoc (rest, Arg (_, xs, _)) ->
        union_blockers (arg_blockers rest) (Option.to_list (blocker_of (CubeOf.find_top xs).tm))
    | Snoc (rest, Field _) -> arg_blockers rest
    | Snoc (rest, Inst _) -> arg_blockers rest in
  match (blocker_of x, x) with
  | Some b, Neu { head = Live _; args; _ } -> union_blockers [ b ] (arg_blockers args)
  | _ -> []

(* A failure to compare two values is stuck if either of them is blocked on a metavariable, even if the mismatch that was found is not.  If neither is, we return the failure unchanged. *)
let stuck_on : type mode s t. (mode, s) value -> (mode, t) value -> failure -> failure =
 fun x y err ->
  match union_blockers (blockers_of x) (blockers_of y) with
  | [] -> err
  | blockers -> (
      match err with
      | Unequal why -> Stuck (why, blockers)
      | Stuck (why, inner) -> Stuck (why, union_blockers inner blockers))

(* Compare two normal forms that are *assumed* to have the same type, or at least that the type of the first is a subtype of the type of the second. *)
let rec equal_nf : type mode a b. (mode, a, b) Ctx.t -> mode normal -> mode normal -> unit Err.t =
 fun n x y ->
  (* Thus, we can do an eta-expanding check at either one of their stored types, since they are assumed equal.  We check them at the type of the *second* argument, since this is also called as a subroutine of subtype checking, in which case the subtype comes first and then the supertype. *)
  equal_at n x.tm y.tm (Lazy.force y.ty)

(* At a type with an eta-rule, two neutrals with equal spines are nevertheless equal, and checking this first can avoid an eta-expansion.  This matters especially with glued evaluation, where parallel derivations produce equal retained spines that are not physically shared, and where eta-expanding compares (and hence unfolds and re-evaluates) their realizations instead.  A spine mismatch is inconclusive at an eta type, so callers fall back to eta-expanding. *)
and equal_at_eta_spines : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) value -> (mode, kinetic) value -> bool =
 fun ctx x y ->
  match (x, y) with
  | Neu _, Neu _ -> (
      (* Since the fallback is to something else that is complete, this should never solve anything. *)
      match flexibly (fun () -> equal_neu ctx x y) with
      | Ok () -> true
      | Error _ -> false)
  | _ -> false

(* Compare two neutrals as spines, without solving any metavariables if the comparison might be abandoned.  If that fails, then the mismatch is inconclusive if either side unfolds (its stored value is Realized), in which case we call the given function on the unfoldings.  Since view_term unfolds Realized glued values all the way down, a second view is the physical identity, so there is at most one retry per node and subterms that match as spines are never unfolded.  Otherwise, if the spines are forced to be equal, we compare them again, now solving metavariables. *)
and equal_neu_or_unfold : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    ((mode, kinetic) value -> (mode, kinetic) value -> unit Err.t) ->
    unit Err.t =
 fun ctx x y retry ->
  match flexibly (fun () -> equal_neu ctx x y) with
  | Ok () -> Ok ()
  | Error err -> (
      let vx = view_term x in
      let vy = view_term y in
      if vx != x || vy != y then retry vx vy
      else if not (Global.unsolved_unifs ()) then Error err
      else if forces_spine x && forces_spine y then
        if !flexible then Error err
        else equal_neu ctx x y
          (* If a spine isn't forced to be equal, then the comparison is stuck, unless we can make progress below. *)
      else if !flexible then Error (stuck_on x y err)
      else
        (* Even if the spines aren't forced to be equal, the instantiation arguments of a type are.  Comparing them, with their types, may solve the metavariable that is blocking the comparison, as with ?X in "Id ?X ?x ?y" and "Id A a b", since that metavariable appears in the types of those arguments even though it doesn't appear in the type of the instantiated type. *)
        match equal_instantiations ctx x y with
        | None -> Error (stuck_on x y err)
        | Some (Error _ as result) -> result
        | Some (Ok ()) -> (
            let vx = view_term x in
            let vy = view_term y in
            if vx != x || vy != y then retry vx vy
            else
              match flexibly (fun () -> equal_neu ctx x y) with
              | Ok () -> Ok ()
              | Error _ ->
                  (* The types that are being instantiated must also be equal, which may solve a metavariable that is itself a higher-dimensional type. *)
                  let mode = Ctx.mode ctx in
                  equal_nf ctx (uninstantiate mode x) (uninstantiate mode y)))

(* Compare the instantiation arguments of two types that are both instantiated, comparing the types of those arguments first. *)
and equal_instantiations : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) value -> (mode, kinetic) value -> unit ErrOpt.t =
 fun ctx x y ->
  match (x, y) with
  | Neu { args = Snoc (_, Inst (_, a1)); _ }, Neu { args = Snoc (_, Inst (_, a2)); _ } ->
      equal_tyargs ~types:true ctx a1 a2
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
  if x == y then Ok ()
  else
    with_solver ctx x y (Some ty) @@ fun () ->
    (* The type must be fully instantiated. *)
    match view_type ty "equal_at" with
    (* The only interesting thing here happens when the type is one with an eta-rule, such as a pi-type. *)
    | Canonical (_, Pi { x = name; filter; doms; cods }, ins, tyargs) ->
        if equal_at_eta_spines ctx x y then Ok ()
        else
          let modality = Modality.filter_modality filter in
          let Eq = eq_of_ins_zero ins in
          let newargs, newnfs = dom_vars ctx modality doms in
          let (Any_ctx newctx) =
            Ctx.variables_vis ctx (Modality.filter_idempotent filter) name newnfs in
          let output = tyof_app cods tyargs filter newargs in
          (* If both terms have the given pi-type, then when applied to variables of the domains, they will both have the computed output-type, so we can recurse back to eta-expanding equality at that type. *)
          equal_at newctx (apply_term x filter newargs) (apply_term y filter newargs) output
    (* Codatatypes (without eta) don't need to be dealt with here, even though structs can't be compared synthesizingly, since codatatypes aren't actually inhabited by (kinetic) structs, only neutral terms that are equal to potential structs.  In the case of record types with eta, if there is a nonidentity insertion outside, then the type isn't actually a record type, *but* it still has an eta-rule since it is *isomorphic* to a record type!  Thus, instead of checking whether the insertion is the identity, we apply its inverse permutation to the terms being compared.  And because we pass off to 'field' and 'tyof_field', we don't need to make explicit use of any of the other data here. *)
    | Canonical
        (type hmode mn m n)
        ((_, Codata (type a et) ({ eta; fields; _ } : (mode, m, n, a, et) codata_args), ins, _) :
          hmode head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t) -> (
        match eta with
        | Eta ->
            if equal_at_eta_spines ctx x y then Ok ()
            else
              let (Perm_to p) = perm_of_ins ins in
              let pinv = deg_of_perm (perm_inv p) in
              let x, y, ty =
                let idc = Modalcell.id2 (Ctx.mode ctx) in
                (act_value x pinv idc, act_value y pinv idc, gact_ty None ty pinv idc) in
              (* Now we take the projections and compare them at appropriate types.  It suffices to use the fields of x when computing the types of the fields, since we proceed to check the fields for equality *in order* and thus by the time we are checking equality of any particular field of x and y, the previous fields of x and y are already known to be equal, and the type of the current field can only depend on these.  (This latter is a semantic constraint on the kinds of generalized records that can sensibly admit eta-conversion.)  In addition, records with eta cannot have higher fields, so as field insertion it suffices to use ins_zero on the substitution dimension. *)
              let fldins = ins_zero (cod_left_ins ins) in
              let rec do_fields = function
                | Bwd.Emp -> return ()
                | Snoc
                    ( fields,
                      CodatafieldAbwd.Entry
                        (type i)
                        ((fld, Codatafield (_, adj, _, Lower _)) :
                          i Field.t * (i, mode * a * D.zero * n * has_eta) Codatafield.t) ) -> (
                    let* () = do_fields fields in
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
                          (tyof_field left xu tyu fld fldins)) in
              do_fields fields
        (* At a codatatype without eta, there are no kinetic structs, only comatches, and those are not compared componentwise, only as neutrals, since they are generative. *)
        | Noeta -> equal_val ctx x y)
    (* At an ordinary datatype, two constructors are equal if they are instances of the same constructor, with the same dimension and arguments.  We handle these cases here because we can use the datatype information to give types to the arguments of the constructor. *)
    | Canonical (_, Data { constrs; _ }, ins, tyargs) ->
        let Eq = eq_of_ins_zero ins in
        equal_at_data ctx constrs ty tyargs x y
    (* If the type is not one that has an eta-rule, then we pass off to a synthesizing equality-check, forgetting about our assumption that the two terms had the same type.  This is the equality-checking analogue of the conversion rule for checking a synthesizing term, but since equality requires no evidence we don't have to actually synthesize a type at which they are equal or verify that it equals the type we assumed them to have. *)
    | _ -> equal_val ctx x y

(* At an ordinary datatype, compare two terms that are assumed to have that datatype as their type (given by 'constrs', 'ty', and 'tyargs', as extracted from the type by 'equal_at').  With glued evaluation, terms at a datatype may be glued neutrals whose values unfold to constructors.  We compare the terms as given, and only if that is inconclusive (a neutral spine mismatch, or a shape mismatch) do we unfold with view_term and retry.  Since view_term unfolds Realized glued values all the way down, a second view is the physical identity and the retry recursion terminates. *)
and equal_at_data : type mode m a b.
    (mode, a, b) Ctx.t ->
    (Constr.t, (mode, m) dataconstr) Abwd.t ->
    (mode, kinetic) value ->
    (D.zero, m, m, mode normal) TubeOf.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    unit Err.t =
 fun ctx constrs ty tyargs x y ->
  match (x, y) with
  | Constr (xconstr, xn, xargs), Constr (yconstr, yn, yargs) -> (
      let (Dataconstr { env = _; ty = _; fnty }) =
        match Abwd.find_opt xconstr constrs with
        | Some x -> x
        | None -> fatal (Anomaly "constr not found in equality-check") in
      let* () = guard (xconstr = yconstr) (Unequal.Constrs (xconstr, yconstr)) in
      match (D.compare xn yn, D.compare xn (TubeOf.inst tyargs)) with
      | Neq, _ -> fatal (Dimension_mismatch ("equality of constrs", xn, yn))
      | _, Neq -> fatal (Dimension_mismatch ("equality of constrs", xn, TubeOf.inst tyargs))
      | Eq, Eq ->
          let (Wrap xargs) = Vec.of_list xargs in
          let lgth = Vec.length xargs in
          let yargs =
            Vec.of_list_length lgth yargs
            <|> Anomaly "wrong number of constructor arguments in equality-check" in
          (* The instantiation must be at other instances of the same constructor; we take its arguments as in 'check'. *)
          let tyarg_args =
            find_tyarg_args ~check_dim:"equality of constrs" xconstr lgth tyargs
              ~wrong_arity:(fun () -> Anomaly "inst arg wrong num args in readback at datatype")
              ~wrong_constr:(fun _ -> Anomaly "inst arg wrong constr in equality at datatype")
              ~not_constr:(fun _ -> Anomaly "inst arg not constr in equality at datatype") in
          (* It suffices to compare the top-dimensional faces of the cubes; the others are only there for evaluating case trees. *)
          equal_at_pi ctx xn (lazy (force_eval_term fnty)) xargs yargs tyarg_args)
  (* Two neutrals are first compared as spines; if they unfold, the unfoldings may now be constructors. *)
  | Neu _, Neu _ -> equal_neu_or_unfold ctx x y (equal_at_data ctx constrs ty tyargs)
  | _ -> (
      let vx = view_term x in
      let vy = view_term y in
      if vx != x || vy != y then equal_at_data ctx constrs ty tyargs vx vy
      else
        match (x, y) with
        (* A failed term can't be compared with a constructor, any more than with a neutral (see equal_head). *)
        | Neu { head = Failed _; _ }, _ | _, Neu { head = Failed _; _ } ->
            fatal (Dependent "comparing a failed term")
        (* A constructor is unequal to a neutral, unless the neutral is blocked on a metavariable whose solution might make it compute to that constructor. *)
        | Constr _, _ | _, Constr _ ->
            Error
              (stuck_on x y
                 (Unequal
                    (Terms
                       ( PNormal (ctx, { tm = x; ty = Lazy.from_val ty }),
                         PNormal (ctx, { tm = y; ty = Lazy.from_val ty }) ))))
        | _ -> equal_val ctx x y)

(* "Synthesizing" equality check of two values, now *not* assumed a priori to have the same type.  If this function concludes that they are equal, then the equality of their types is part of that conclusion. *)
and equal_val : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) value -> (mode, kinetic) value -> unit Err.t =
 fun ctx x y ->
  if x == y then Ok ()
  else
    with_solver ctx x y None @@ fun () ->
    match (x, y) with
    | Neu _, Neu _ -> equal_neu_or_unfold ctx x y (equal_val ctx)
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
  (* A failed term is unequal to everything, but this is a consequence of the failure, so we fail silently. *)
  | Neu { head = Failed _; _ }, _ | _, Neu { head = Failed _; _ } ->
      fatal (Dependent "comparing a failed term")
  | ( Neu { head = Live head1; args = apps1; value = _; ty = _ },
      Neu { head = Live head2; args = apps2; value = _; ty = _ } ) -> (
      (* To check two neutral applications are equal, with their types, we check if the functions are equal, including their types and hence also their domains and codomains (and also they have the same insertion applied outside).  We don't need to check that the types agree; this procedure concludes equality of types rather than assumes it. *)
      match (nonmodal_apps apps1, nonmodal_apps apps2) with
      (* If neither spine crosses a modal field projection, the heads are at the ambient mode and we can compare them first (as we always did before modal fields), which gives more precise "unequal heads" error messages. *)
      | Some Eq, Some Eq -> (
          match equal_head ctx head1 head2 with
          | Some (Error err) -> Error (map_why (fun why -> Heads why) err)
          | None ->
              let h1, h2 = (readback_head ctx head1, readback_head ctx head2) in
              fail (Heads (Terms (PTerm (ctx, h1), PTerm (ctx, h2))))
          | Some (Ok ()) -> (
              match equal_apps ctx apps1 apps2 with
              | None -> fail (Terms (PVal (ctx, x), PVal (ctx, y)))
              | Some x -> x))
      (* Otherwise, the heads live at the mode at the head end of the spine, so the head comparison happens at the bottom of the spine recursion, in the context locked by the modal field projections crossed on the way. *)
      | _ -> (
          match equal_apps ctx apps1 apps2 ~heads:(head1, head2) with
          | None -> fail (Terms (PVal (ctx, x), PVal (ctx, y)))
          | Some x -> x))
  | Lam _, _ | _, Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing equality-check")
  | Struct _, _ | _, Struct _ -> fatal (Anomaly "unexpected struct in synthesizing equality-check")
  | Constr _, _ | _, Constr _ -> fatal (Anomaly "unexpected constr in synthesizing equality-check")

and equal_tyargs : type mode n1 k1 nk1 n2 k2 nk2 a b.
    ?types:bool ->
    (mode, a, b) Ctx.t ->
    (n1, k1, nk1, mode normal) TubeOf.t ->
    (n2, k2, nk2, mode normal) TubeOf.t ->
    unit ErrOpt.t =
 fun ?(types = false) n a1 a2 ->
  match
    (D.compare (TubeOf.inst a1) (TubeOf.inst a2), D.compare (TubeOf.uninst a1) (TubeOf.uninst a2))
  with
  | Eq, Eq ->
      let Eq = D.plus_uniq (TubeOf.plus a1) (TubeOf.plus a2) in
      (* Because instantiation arguments are stored as normals, we use type-sensitive equality to compare them. *)
      Some
        (short_circuit_err (fun check ->
             TubeOf.miter
               {
                 it =
                   (fun _ [ x; y ] ->
                     if types then check (equal_val n (Lazy.force x.ty) (Lazy.force y.ty));
                     check (equal_nf n x y));
               }
               [ a1; a2 ]))
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
        Some (fail (Variables (PTerm (ctx, readback_head ctx x), PTerm (ctx, readback_head ctx y))))
  | Const { name = c1; ins = i1 }, Const { name = c2; ins = i2 } -> (
      let* () = Some (guard (c1 = c2) (Unequal.Constants (c1, c2))) in
      match D.compare (cod_left_ins i1) (cod_left_ins i2) with
      | Eq ->
          let To d1, To d2 = (deg_of_ins i1, deg_of_ins i2) in
          let* () = ErrOpt.of_opt (deg_equiv d1 d2) in
          return ()
      | Neq -> None)
  | ( Meta { meta = meta1; kind = kind1; env = env1; ins = i1 },
      Meta { meta = meta2; kind = _; env = env2; ins = i2 } ) -> (
      match (Meta.compare meta1 meta2, D.compare (cod_left_ins i1) (cod_left_ins i2)) with
      | Eq, Eq ->
          let To d1, To d2 = (deg_of_ins i1, deg_of_ins i2) in
          let* () = ErrOpt.of_opt (deg_equiv d1 d2) in
          Some (equal_env ctx env1 env2 (Global.meta_termctx meta1 kind1))
      | Neq, _ -> Some (fail (Metas (meta1, meta2)))
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
            (short_circuit_err (fun check ->
                 CubeOf.miter
                   { it = (fun _ [ x; y ] -> check (equal_val lctx x y)) }
                   [ dom1s; dom2s ];
                 (* We create variables for all the domains, in order to equality-check all the codomains.  The codomain boundary types only use some of those variables, but it doesn't hurt to have the others around. *)
                 let newargs, newnfs = dom_vars ctx modality1 dom1s in
                 let (Any_ctx newctx) =
                   Ctx.variables_vis ctx (Modality.filter_idempotent filter1) name newnfs in
                 (* We compare the two cubes of codomains with the binary iterator miter2, which recurses directly on the two trees.  We cannot use the generic n-ary miter [ cod1s; cod2s ] here: iterating two cubes whose element family (BindFam) is a multi-parameter GADT via the heterogeneous Tlist machinery sends type inference into a catastrophic blowup (~15s and 14GB to compile this one expression). *)
                 BindCube.miter2
                   {
                     it2 =
                       (fun s (BindFam cod1) (BindFam cod2) ->
                         let (Filter_sface (fb, kfilter)) = Modality.filter_sface filter1 s in
                         let sargs = CubeOf.subcube fb newargs in
                         check
                           (equal_val newctx
                              (apply_binder_term cod1 kfilter sargs)
                              (apply_binder_term cod2 kfilter sargs)));
                   }
                   cod1s cod2s))
      | Neq, _ | _, Neq -> None)
  | _, _ -> None

(* Check that the arguments of two entire application spines of equal functions are equal.  This is basically a left fold, but we make sure to iterate from left to right, and fail rather than raising an exception if the lists have different lengths.  As noted above, here we can go back to *assuming* that they have equal types, and thus passing off to the eta-expanding equality check.  If heads are supplied, they are compared at the bottom of the recursion, where the context has been locked by the left adjoints of any modal field projections crossed on the way in, so that it lives at the heads' mode. *)
and equal_apps : type h1 h2 mode any1 any2 a b.
    (mode, a, b) Ctx.t ->
    ?heads:h1 head * h2 head ->
    (h1, mode, any1, live) apps ->
    (h2, mode, any2, live) apps ->
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
          | Some (Error err) -> Some (Error (map_why (fun why -> Heads why) err))
          | None ->
              let t1, t2 = (readback_head ctx head1, readback_head ctx head2) in
              Some (fail (Heads (Terms (PTerm (ctx, t1), PTerm (ctx, t2)))))))
  | Snoc (rest1, Arg (filter1, a1, i1)), Snoc (rest2, Arg (filter2, a2, i2)) -> (
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
              Some
                (short_circuit_err (fun check ->
                     CubeOf.miter { it = (fun _ [ x; y ] -> check (equal_nf lctx x y)) } [ a1; a2 ]))
          (* If the dimensions don't match, it is a bug rather than a user error, since they are supposed to both be valid arguments of the same function, and any function has a unique dimension. *)
          | Neq ->
              fatal
                (Dimension_mismatch ("application in equality-check", CubeOf.dim a1, CubeOf.dim a2))
          ))
  | Snoc (rest1, Field (filter1, f1, _, i1)), Snoc (rest2, Field (filter2, f2, _, i2)) -> (
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
          | Neq -> Some (fail (Fields (f1, f2)))))
  | Snoc (rest1, Inst (_, a1)), Snoc (rest2, Inst (_, a2)) ->
      let* () = equal_apps ctx rest1 rest2 ?heads in
      equal_tyargs ctx a1 a2
  | _, _ -> None

and equal_at_pi : type mode n b c d.
    (mode, c, d) Ctx.t ->
    n D.t ->
    (mode, kinetic) value Lazy.t ->
    ((n, mode, kinetic) modal_value_cube, b) Vec.t ->
    ((n, mode, kinetic) modal_value_cube, b) Vec.t ->
    ((D.zero, n, n, (mode, kinetic) modal_value) TubeOf.t, b) Vec.t ->
    unit Err.t =
 fun ctx n fnty xs ys tyargs ->
  match (xs, ys, tyargs) with
  | [], [], [] -> Ok ()
  | Modal (xfilter, x) :: xs, Modal (yfilter, y) :: ys, tyargs :: tyargs_rest -> (
      (* The constructor's function-type value must be a pi-type; we compare the arguments at its domain (instantiated at the corresponding arguments of the lower-dimensional constructors) and continue with the codomain applied to the argument cube. *)
      let (Viewed_pi { x = _; filter; doms; cods }) = view_pi "equal_at_pi" n (Lazy.force fnty) in
      let pimod = Modality.filter_modality filter in
      let xmodality = Modality.filter_modality xfilter in
      let ymodality = Modality.filter_modality yfilter in
      match (Modality.compare xmodality pimod, Modality.compare ymodality pimod) with
      | Eq, Eq ->
          let Eq = Modality.filter_uniq xfilter filter in
          let Eq = Modality.filter_uniq yfilter filter in
          let (Locked (_, lctx)) = Ctx.lock ctx pimod in
          let x = CubeOf.find_top x in
          let y = CubeOf.find_top y in
          let tyarg = modal_boundary_tube "equal_at_pi" n filter doms tyargs in
          let ity = inst (CubeOf.find_top doms) tyarg in
          let* () = equal_at lctx x y ity in
          let argcube = TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x) in
          let (BindFam b) = BindCube.find_top cods in
          equal_at_pi ctx n (lazy (apply_binder_term b filter argcube)) xs ys tyargs_rest
      | Neq, _ -> fatal (Modality_mismatch (`Internal, "equal_at_pi", xmodality, pimod))
      | _, Neq -> fatal (Modality_mismatch (`Internal, "equal_at_pi", ymodality, pimod)))

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
  | Emp _ -> Ok ()
  (* A weakening entry contributes nothing to the environment, so we skip it. *)
  | Weaken (envctx, _) -> equal_ordered_env ctx env1 env2 envctx
  | Ext (envctx, ({ plus_lock = dplus; bindings; _ } as entry), _, comp) -> (
      match ext_kind entry comp with
      (* An alias contributes nothing to the environment, so we skip it. *)
      | Ext_alias -> equal_ordered_env ctx env1 env2 envctx
      | Ext_dim ->
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
          let lenv = lock_env aenv1 dplus in
          let env1' = remove_top env1 in
          let env2' = remove_top env2 in
          let* () = equal_ordered_env ctx env1' env2' envctx in
          let xtytbl = Hashtbl.create 10 in
          short_circuit_err (fun check ->
              CubeOf.miter
                {
                  it =
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
                                   Hashtbl.find xtytbl
                                     (SFace_of (comp_sface fb (sface_of_tface fc))));
                             }) in
                      Hashtbl.add xtytbl (SFace_of fb) { tm = tm1; ty = Lazy.from_val ty };
                      check (equal_at lctx tm1 tm2 ty));
                }
                [ xs1; xs2 ]))
  | Lock (envctx, g) ->
      let locks = plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g in
      let (Restrict_keys (env1, pre1)) = restrict_keys env1 locks in
      let (Restrict_keys (env2, pre2)) = restrict_keys env2 locks in
      let* () = guard (prekey_equal pre1 pre2) (Unequal.Cells (pre1, pre2)) in
      (* The (equal) prekey actions mediate between a context locked by their vertical source and the actual ambient context, locked by their vertical target.  So we remove the prekey's target from the context and re-lock with its source (both no-ops when there was no prekey) before removing the lock itself. *)
      let (Remove_lock (ctx, _)) = Ctx.remove_lock ctx (Modalcell.vtgt pre1) in
      let (Locked (_, ctx)) = Ctx.lock ctx (Modalcell.vsrc pre1) in
      let (Remove_lock (ctx, _)) = Ctx.remove_lock ctx (Modality.of_gen g) in
      equal_ordered_env ctx env1 env2 envctx
