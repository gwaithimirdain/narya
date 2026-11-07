open Bwd
open Util
open Modal
open Tbwd
open Reporter
open Dim
open Tctx
open Term
open Value
open Env
open Domvars
open Act
open Norm
open Printable
module Binding = Ctx.Binding

(* The "Displaying" reader records whether we're reading back for printing to the user or for internal purposes.  For instance, when printing we do more eta-expansion if the user requested it.  Wrapping the "Displaying" module in another module called "Readback" and opening that module allows us to refer to the module as just "Displaying" here, but exports it as "Readback.Displaying" to other files even when they open this file. *)

(* When reading back the solution of a unification metavariable, we record that metavariable and which levels are undefined in its renamed context because they are the image of more than one variable or of one with the wrong annotation (see renamed_ctx), as opposed to outside the image of its renaming altogether. *)
type unifying = { target : Meta.wrapped; undefined : level -> bool; under_rigid : bool }

module Readback = struct
  module Displaying = Algaeff.Reader.Make (Bool)

  (* The "Unifying" reader records whether we're reading back a value to be the solution of a unification metavariable, and if so which one.  In that case the readback must fail, by raising Unsolvable, if the value refers to a variable that isn't in the context (since the solution lives in the smaller context of the metavariable), or if it contains the metavariable itself, either directly or through the definition of some other metavariable.  To avoid the latter, we unfold all solved unification metavariables and all definition metavariables of the current origin (such as let-bound variables), failing if any of the latter don't have a value to unfold to. *)
  module Unifying = Algaeff.Reader.Make (struct
    type t = unifying option
  end)

  (* A readback failure is rigid if the value can't be the solution of the metavariable however any other metavariables are solved, because the metavariable itself or a variable outside the image of its renaming occurs in a rigid position: not inside a neutral that is stuck on a metavariable or that might unfold, and not at a singleton type, where it could be replaced by anything else.  Otherwise it is flexible. *)
  exception Unsolvable of [ `Rigid | `Flexible ]
end

open Readback

let () =
  Displaying.register_printer (function `Read -> Some "unhandled Readback.Displaying.read effect");
  Unifying.register_printer (function `Read -> Some "unhandled Readback.Unifying.read effect")

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

(* When a degeneracy acts on a variable or constant, the name it is displayed with (e.g. "refl", "Id", or "ap") depends on the sort of the *type of that variable or constant*, not on the type of the whole neutral application in which it occurs.  Since this only affects display, and computing it involves evaluating and descending through pi-types, we catch any errors and fall back on the generic name (though internal errors are still reported).  We can compute it in an empty context of the appropriate mode, since sort_of_ty uses the context only to create new variables. *)
let sort_of_val : type mode. mode Mode.t -> (mode, kinetic) value -> [ `Type | `Function | `Other ]
    =
 fun mode ty ->
  Reporter.discard_errors ~fallback:(fun () -> `Other) @@ fun () ->
  sort_of_ty (Ctx.empty mode) (view_type ty "sort_of_val")

(* Whether a constant is defined to be a canonical type, possibly a family of them.  Such a constant is displayed with a superscript degeneracy rather than a name like "Id", even if the term in which it appears is not itself a type (e.g. a field projection out of a degenerated record type). *)
let rec is_canonical_def : type mode a. (mode, a, potential) term -> bool = function
  | Canonical _ -> true
  | Lam (_, _, _, body) -> is_canonical_def body
  | _ -> false

let is_canonical_const : Constant.t -> [ `Canonical | `Other ] =
 fun c ->
  Reporter.discard_errors ~fallback:(fun () -> `Other) @@ fun () ->
  let (Definition { tm; _ }) = Global.find_const c in
  match tm with
  | `Defined tm when is_canonical_def tm -> `Canonical
  | _ -> `Other

(* The same question for a term rather than a value, by looking at the head of its application spine.  This is used when annotating a degeneracy at typechecking time, so that a term displayed without being read back (e.g. by the "synth" command) is displayed the same way as one that is read back. *)
let rec canonical_head : type mode a s. (mode, a, s) term -> [ `Canonical | `Other ] = function
  | Const c -> is_canonical_const c
  | App (_, fn, _, _, _) -> canonical_head fn
  | Inst (_, tm, _) -> canonical_head tm
  | Act (_, tm, _, _) -> canonical_head tm
  | Key { tm; _ } -> canonical_head tm
  | _ -> `Other

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

(* Whether the top entry of an environment is the identity environment of a context entry with the given modality and bindings, because the environment is a context whose top entry has those very bindings. *)
let rec is_top_bindings : type mode n d dom modality k.
    (mode, n, d) env -> (dom, modality, mode) Modality.t -> (k, dom Binding.t) CubeOf.t -> bool =
 fun env modality bindings ->
  match env with
  | Ctx (Snoc (ctx, entry, _, comp)) -> (
      match Ctx.Ordered.ext_kind entry comp with
      (* An alias isn't part of the environment. *)
      | Ext_alias -> is_top_bindings (Ctx ctx) modality bindings
      | Ext_dim -> (
          match
            ( Modality.compare (Ctx.modality_entry entry) modality,
              D.compare (Ctx.dim_entry entry) (CubeOf.dim bindings) )
          with
          | Eq, Eq -> Ctx.bindings_entry entry == bindings
          | _ -> false))
  | Ctx (Weaken (ctx, _)) -> is_top_bindings (Ctx ctx) modality bindings
  | _ -> false

(* Test whether a zero-dimensional environment for a metavariable's context is the identity environment of an ordered context (the one we are reading back in), i.e. whether the two contexts have the same shape and each entry of the environment is the value of the corresponding variable in that context.  If so, we return the resulting equality of checked lengths, built up entry by entry as we compare the shapes.  This is a conservative test: a free variable must appear literally, as a variable with the same level and no degeneracy, key, or arguments, while a let-bound variable must have its own value, up to physical equality.  Usually, though, the environment is (a weakening of) the context itself, which we can recognize entry by entry without looking anything up.  It is used to read back a metavariable whose environment is the identity as a plain Meta, rather than wrapped in a let-only. *)
let rec is_identity_ordered_env : type mode a b d.
    (mode, a, b) Ctx.Ordered.t -> (mode, D.zero, d) env -> (mode, d) Tctx.t -> (b, d) Eq.t option =
 fun ctx env envctx ->
  match (ctx, envctx) with
  (* Weakening entries and aliases contribute nothing to the checked length or the environment. *)
  | Weaken (ctx, _), _ -> is_identity_ordered_env ctx env envctx
  | Snoc (ctx, _, _, Zero), _ -> is_identity_ordered_env ctx env envctx
  | Emp _, Path (Suc (Zero, Proj _), _) -> Some Eq
  (* Locks we test for equality and then remove from both contexts and the environment. *)
  | Lock (ctx, g), Path (Suc (envctx, Lock g'), o) -> (
      match Modality.Gen.compare g g' with
      | Neq -> None
      | Eq ->
          let (Restrict_keys (env, pre)) =
            restrict_keys env (plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g)
          in
          (* Any nonidentity prekey encountered in the environment means it is not an identity. *)
          if Modalcell.is_id pre then
            match is_identity_ordered_env ctx env (Path (envctx, o)) with
            | Some Eq -> Some Eq
            | None -> None
          else None)
  | Snoc (ctx, entry, _, comp), Path (Suc (envctx, Dim (tk, tfilter)), o) -> (
      match Ctx.Ordered.ext_kind entry comp with
      | Ext_alias -> None
      | Ext_dim -> (
          let modality = Ctx.modality_entry entry in
          let bindings = Ctx.bindings_entry entry in
          let k = CubeOf.dim bindings in
          match (Modality.compare modality (Modality.filter_modality tfilter), D.compare k tk) with
          | Eq, Eq -> (
              let exception Not_identity in
              try
                (* If the environment's top entry is itself physically equal to this entry of the context, there is nothing to look up. *)
                (if is_top_bindings env modality bindings then ()
                 else if Option.is_none (Binding.value_opt (CubeOf.find_top bindings)) then
                   (* If the entry is not yet determined (as while reading back its own bindings in readback_entry), it can't match, so we don't bother looking anything up. *)
                   raise_notrace Not_identity
                 else
                   (* Otherwise we look up the top entry in the environment and check whether it is "the same as" the one in the context in a weaker sense. *)
                   let (Looked_up { act; op; entry = xs; pre }) =
                     lookup_cube env (D.zero_plus k) modality modality Now (id_opt_op k) in
                   (* For free variables, we check that they have the same level and identity degeneracies and keys; for let-bound variables we check that their defined values are physically equal (skipping a costly semantic-equality check).  Neither of these can succeed if the looked up value has a nonidentity operation or key on it, since the act functions only return physically equal values if they short-circuit; so we wait to force the value with "act" until checking those.  (We do still need to call "act" even though the actions are identities, because lookup_cube returns an abstract type that we have to force into a value.) *)
                   match (is_id_opt_op op, Modalcell.is_id pre) with
                   | Some Eq, true ->
                       let s = id_deg k in
                       CubeOf.miter2
                         {
                           it2 =
                             (fun _ x b ->
                               if
                                 not
                                   (match (Binding.level b, Binding.value_opt b) with
                                   (* A free variable's value is itself, except in a renamed context, where it may be a permutation of a variable (see renamed_var), and then a plain occurrence of that variable is not the same as the variable bound here. *)
                                   | Some level, Some v ->
                                       is_plain_var level v.tm && is_plain_var level (act x s pre)
                                   | Some level, None -> is_plain_var level (act x s pre)
                                   | None, Some v -> v.tm == act x s pre
                                   | None, None -> false)
                               then raise_notrace Not_identity);
                         }
                         xs bindings
                   | _ -> raise_notrace Not_identity);
                (* If we get here, the top environment entry succeded in matching the context entry, so we recurse. *)
                match is_identity_ordered_env ctx (remove_top env) (Path (envctx, o)) with
                | Some Eq -> Some Eq
                | None -> None
              with Not_identity -> None)
          | _ -> None))
  | _ -> None

(* The ways we can read back a metavariable whose environment is the identity, possibly weakened. *)
type (_, _, _) meta_readback =
  (* The metavariable itself weakened, in which case we have to reconstruct both parts of a weaken operation. *)
  | Weakened_meta :
      ('a, 'amode, 'mu, 'mode, 'd) plus_lock * ('a, 'amode, 'mu, 'mode, 'b) plus_with_locks
      -> ('mode, 'd, 'b) meta_readback
  (* A let-bound variable, in some face of a cube, whose value is the metavariable, in which case we only need the plus_with_locks to supply to Var, but also the face and filter. *)
  | Let_var :
      (('a, ('modality, 'k) dim_entry) snoc, 'xmode, 'mu, 'mode, 'b) plus_with_locks
      * ('m, 'k) sface
      * ('dom, 'modality, 'xmode, 'k, 'k) Modality.filter_dim
      -> ('mode, 'd, 'b) meta_readback

(* Test whether a zero-dimensional environment for a metavariable's context is the identity on that context weakened by some entries of the given ordered context, each of which may lie behind locks matching ones in the metavariable's context.  This is the same search as in find_meta_readback below, except that we don't look for variables let-bound to the metavariable. *)
let rec is_weakened_identity : type mode a b d.
    (mode, a, b) Ctx.Ordered.t -> (mode, D.zero, d) env -> (mode, d) Tctx.t -> bool =
 fun ctx env envctx ->
  Option.is_some (is_identity_ordered_env ctx env envctx)
  ||
  match (ctx, envctx) with
  | Snoc (rest, _, _, _), _ -> is_weakened_identity rest env envctx
  | Weaken (rest, _), _ -> is_weakened_identity rest env envctx
  | Lock (ctx, g), Path (Suc (envctx, Lock g'), o) -> (
      match Modality.Gen.compare g g' with
      | Neq -> false
      | Eq ->
          let (Restrict_keys (env, pre)) =
            restrict_keys env (plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g)
          in
          Modalcell.is_id pre && is_weakened_identity ctx env (Path (envctx, o)))
  | _ -> false

(* Test whether some face of a context entry is a variable that is let-bound to a given metavariable (whose full context is given) in an environment that is the identity, possibly weakened, on the context to its left locked by the modality of the variable, and whether the given environment for that metavariable (with the locks to the right of the variable stripped off) is also a weakened identity on the context to its left.  If so, return that face.  (The metavariable can be defined in a context shorter than the one to the left of the variable, as happens for the variables bound by a let-rec, whose metavariables all live in the context of the let-rec.) *)
let let_var_of_meta : type mode a b d x s mmode dfull dom modality f k b2.
    (mmode, x, dfull, s) Meta.t ->
    (mmode, dfull) Tctx.t ->
    (mode, a, b) Ctx.Ordered.t ->
    (dom, modality, mode, f, k, b2) Ctx.entry ->
    (mode, D.zero, d) env ->
    (mode, d) Tctx.t ->
    k sface_of option =
 fun meta fullctx ctx entry env envctx ->
  let modality = Ctx.modality_entry entry in
  let is_let_var : dom Binding.t -> bool =
   fun b ->
    match (Binding.level b, Binding.value_opt b) with
    | ( None,
        Some
          { tm = Neu { head = Live (Meta { meta = meta'; env = xenv; ins; _ }); args = Emp; _ }; _ }
      ) -> (
        (* The variable is let-bound to a metavariable, so we compare it to our given one.  We also check whether its environment is 0-dimensional and it has no insertion. *)
        match (Meta.compare meta' meta, D.compare (dim_env xenv) D.zero, is_id_ins ins) with
        | Eq, Eq, Some _ ->
            (* The value of the variable lives in the context locked by its modality. *)
            let (Locked (_, lctx)) = Ctx.Ordered.lock ctx modality in
            (* Both environments also have to be weakened identities on what's left for this sort of readback to be possible. *)
            is_weakened_identity lctx xenv fullctx && is_weakened_identity ctx env envctx
        | _ -> false)
    | _ -> false in
  let result = ref None in
  CubeOf.miter
    {
      it =
        (fun fa [ b ] ->
          if Option.is_none !result && is_let_var b then result := Some (SFace_of fa));
    }
    [ Ctx.bindings_entry entry ];
  !result

(* Search for a way to read back a metavariable whose environment is the identity on the context we are reading back in, possibly weakened by some variables, each of which may lie behind locks. *)
let rec find_meta_readback : type mode a b d x s mmode dfull.
    (mmode, x, dfull, s) Meta.t ->
    (mmode, dfull) Tctx.t ->
    (mode, a, b) Ctx.Ordered.t ->
    (mode, D.zero, d) env ->
    (mode, d) Tctx.t ->
    (mode, d, b) meta_readback option =
 fun meta fullctx ctx env envctx ->
  let open Monad.Ops (Monad.Maybe) in
  let mode = Ctx.Ordered.mode ctx in
  (* We first test whether the environment is exactly the identity of the whole context. *)
  match is_identity_ordered_env ctx env envctx with
  | Some Eq ->
      (* If so, we read back as a Term.Meta, which will have to be weakened by any entries that were stripped off before this.  Note that this case can never be a variable let-bound to the metavariable, since in that case the meta is defined in a shorter context (everything before the variable). *)
      Some (Weakened_meta (plus_no_lock mode, plus_with_no_locks mode))
  | None -> (
      (* If not, and the context ends with a variable, we check whether that variable is let-bound to the metavariable, and if so whether the rest of the environment is also an identity. *)
      match (ctx, envctx) with
      (* An alias isn't a variable, so it can't be read back as one, and it doesn't weaken the checked context. *)
      | Snoc (rest, entry, _, comp), _ -> (
          match Ctx.Ordered.ext_kind entry comp with
          | Ext_alias -> find_meta_readback meta fullctx rest env envctx
          | Ext_dim -> (
              let k = Ctx.dim_entry entry in
              let filter = Ctx.filter_entry entry in
              match let_var_of_meta meta fullctx rest entry env envctx with
              | Some (SFace_of fa) -> Some (Let_var (plus_with_no_locks mode, fa, filter))
              | None -> (
                  (* If not, we remove it from the context and try again, weakening the result if successful. *)
                  match find_meta_readback meta fullctx rest env envctx with
                  | Some (Weakened_meta (plus, newplus)) ->
                      Some (Weakened_meta (plus, plus_with_locks_dim newplus k filter))
                  | Some (Let_var (newplus, fa, f)) ->
                      Some (Let_var (plus_with_locks_dim newplus k filter, fa, f))
                  | None -> None)))
      | Weaken (rest, _), _ -> find_meta_readback meta fullctx rest env envctx
      (* If the context ends with a lock that matches one at the end of the metavariable's context, we remove both and search behind them. *)
      | Lock (ctx, g), Path (Suc (envctx, Lock g'), o) -> (
          match Modality.Gen.compare g g' with
          | Neq -> None
          | Eq ->
              (* We also have to remove that lock from the environment. *)
              let (Restrict_keys (env, pre)) =
                restrict_keys env (plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g)
              in
              (* If removing that lock encounters a prekey, then the environment is not a weakened identity.  Otherwise, we can try again with the locks removed, re-locking the result. *)
              if Modalcell.is_id pre then
                match find_meta_readback meta fullctx ctx env (Path (envctx, o)) with
                | Some (Weakened_meta (plus, newplus)) ->
                    Some (Weakened_meta (plus_lock_suc plus g, plus_with_locks_lock newplus g))
                | Some (Let_var (newplus, fa, filter)) ->
                    Some (Let_var (plus_with_locks_lock newplus g, fa, filter))
                | None -> None
              else None)
      | _ -> None)

(* Check whether the environment on a metavariable is a weakened identity on the context we are reading back in, possibly prekeyed (as happens when a let-bound variable whose value is the metavariable is used with a key).  If so, we can read it back as either a Term.Meta, or a Term.Var if there is a variable let-bound to it, with a Key.  Since this is only an optimization of display, any errors encountered just mean that the search fails. *)
let readback_meta_at_idenv : type mode a b n d x s.
    (mode, a, b) Ctx.t ->
    (mode, x, d, s) Meta.t ->
    (mode, d, s, kinetic) meta_kind ->
    (mode, n, d) env ->
    (mode, b, kinetic) term option =
 fun ctx meta kind env ->
  let open Monad.Ops (Monad.Maybe) in
  let envctx = Meta.tctx meta in
  let search : type a b.
      (mode, a, b) Ctx.t -> (mode, D.zero, d) env -> (mode, b, kinetic) term option =
   fun (Permute { ctx; _ }) env ->
    match find_meta_readback meta envctx ctx env envctx with
    | Some (Weakened_meta (plus, newplus)) ->
        Some (weaken_gen plus (Meta (meta, kind, Kinetic)) newplus)
    | Some (Let_var (newplus, fa, filter)) -> (
        (* The variable can be referred to without a key only if the composite of the locks behind which it lies is its modal annotation. *)
        match
          Modality.compare (Modality.filter_modality filter) (plus_with_locks_modality newplus)
        with
        | Eq -> Some (Var (Index (Now, fa, filter, newplus)))
        | Neq -> None)
    | None -> None in
  Reporter.discard_errors ~fallback:(fun () -> None) @@ fun () ->
  match (D.compare (dim_env env) D.zero, envctx) with
  | Eq, Path (Suc (_, Lock g), _) ->
      let (Restrict_keys (lenv, pre)) =
        restrict_keys env (plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g) in
      if Modalcell.is_id pre then search ctx env
      else
        (* If the context doesn't have the locks that the prekey needs, which can happen when reading back the solution of a unification metavariable, then the search fails. *)
        let* (Remove_lock (kctx, plus_tgt)) = Ctx.remove_lock_opt ctx (Modalcell.vtgt pre) in
        let (Locked (plus_src, kctx)) = Ctx.lock kctx (Modalcell.vsrc pre) in
        let* tm = search kctx (Lock (lenv, g)) in
        return (Key { tm; cell = pre; plus_tgt; plus_src })
  | Eq, _ -> search ctx env
  | Neq, _ -> None

(* Whether a term context has no checked variables, but only aliases and weakenings. *)
let no_checked_vars : type mode b. (mode, b) Tctx.t -> (b, mode emp) Eq.t option = function
  | Path (Suc (Zero, Proj _), _) -> Some Eq
  | _ -> None

(* Readback of values to terms.  Closely follows equality-testing in equal.ml, so most comments are omitted.  However, unlike equality-testing and the "readback" in theoretical NbE, this readback does *not* eta-expand functions and tuples.  It is used for (1) displaying terms to the user, who will usually prefer not to see things eta-expanded, and (2) turning values into terms so that we can re-evaluate them in a new environment, for which purpose eta-expansion is irrelevant.  There are two exceptions:

   1. When reading back at a record type that the user has marked as transparent, we eta-expand tuples.  This is chosen based on the readback type.
   2. When reading back a higher-dimensional pi-type, we eta-expand its instantiation arguments so that we can display it prettily.  This is controlled by the flag ~eta.

   In typechecking we only ever read back kinetic terms.  But reading back potential terms is useful for displaying definitions to the user, so we work as energy-polymorphically as possible.  A case tree that is stuck, however, is not reconstructed: it is displayed as the application spine of the neutral whose value it is. *)

(* Remove locks from a context during readback.  When reading back the solution of a unification metavariable, the context might not have the required locks, which means there is no solution. *)
let remove_lock : type mode modality cod a bc.
    (mode, a, bc) Ctx.t ->
    (mode, modality, cod) Modality.t ->
    (cod, modality, mode, bc) Ctx.remove_lock =
 fun ctx modality ->
  match Ctx.remove_lock_opt ctx modality with
  | Some result -> result
  | None when Option.is_some (Unifying.read ()) -> raise (Unsolvable `Flexible)
  | None -> Ctx.remove_lock ctx modality

(* ********** Primary readback functions ********** *)

(* The result of reading back the bindings in the last entry of a context (see readback_entry): the bindings live in the whole context locked by the modality of the entry. *)
type (_, _, _, _, _, _) readback_entry =
  | Readback_entry :
      ('bb, 'mode, 'modality, 'dom, 'bm) plus_lock
      * ('dom, 'ax, 'bm) Ctx.t
      * ('n, ('dom, 'bm) binding) CubeOf.t
      -> ('mode, 'ax, 'bb, 'modality, 'dom, 'n) readback_entry

(* These functions deal primarily with kinetic values, and with the value types that are shared between kinetic and potential values, but they include hooks to detect when readback of potential values is called for and pass off to those functions defined later. *)

(* In a renamed context (see below), a variable of the metavariable's context may be sent to a permutation p of a variable y of the current context.  Inverting this, y is the inverse permutation of the variable of the metavariable's context, and so a degeneracy acting on y acts on that.  In any other context, the value of a free variable is that variable itself, so this does nothing. *)
let renamed_deg : type mode s m n. (mode, s) value -> (m, n) deg -> any_deg =
 fun value deg ->
  match value with
  | Neu { head = Live (Var { deg = p; _ }); args = Emp; _ } -> (
      match (is_id_deg p, perm_of_deg p) with
      | None, Some p ->
          let (DegExt (_, _, deg)) = comp_deg_extending (deg_of_perm (perm_inv p)) deg in
          Any_deg deg
      | _ -> Any_deg deg)
  | _ -> Any_deg deg

(* When checking whether a value avoids some variables, we may want to know whether it does so up to the solutions of unsolved metavariables, i.e. whether its only occurrences of those variables are inside neutrals that are blocked on metavariables, whose solutions might eliminate them (see Check.check_var_match).  If so, this is set to a function to call with the blocker of such a neutral, which is then read back as a failed term, since the result of such a readback is discarded anyway. *)
let blocked_dependence : (blocker -> unit) option ref = ref None

(* Run a readback, calling the given function on the blocker of each blocked neutral that it can't read back because it refers to a variable not in the context. *)
let with_blocked_dependence (f : blocker -> unit) (readback : unit -> 'a) : 'a =
  let old = !blocked_dependence in
  blocked_dependence := Some f;
  Fun.protect ~finally:(fun () -> blocked_dependence := old) readback

(* When reading back the solution of a unification metavariable, record that we are inside a rigid neutral or constructor. *)
let rigidly (f : unit -> 'a) : 'a =
  Unifying.scope (Option.map (fun u -> { u with under_rigid = true })) f

(* Whether a type is a singleton, which is defined downstream in Unify. *)
type singleton = { test : 'mode 'a 'b. ('mode, 'a, 'b) Ctx.t -> ('mode, kinetic) value -> bool }

let singleton : singleton ref = ref { test = (fun _ _ -> false) }

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
  (* A stuck case tree is displayed as the application spine of the neutral that the status carries, whether it is stuck permanently or only on an unsolved unification metavariable.  Only a potential readback can meet an Unrealized or Blocked, so that neutral is always available. *)
  | (Unrealized | Blocked _), Potential neutral -> Realize (readback_val ctx neutral)

(* A failed term is read back as Failed, whatever its type.  And a term whose type is failed can't be eta-expanded, so we read it back without its type if possible. *)
and readback_at : type mode a z s.
    ?eta:bool ->
    (mode, s) readback_status ->
    (mode, z, a) Ctx.t ->
    (mode, s) value ->
    (mode, kinetic) value ->
    (mode, a, s) term =
 fun ?eta status ctx tm ty ->
  match (tm, ty) with
  | Neu { head = Failed _; _ }, _ -> Failed Kinetic
  | Neu { head = Live _; _ }, Neu { head = Failed _; _ } -> readback_val ctx tm
  | _, Neu { head = Failed _; _ } -> fatal (Dependent "reading back at a failed type")
  | _ -> (
      match Unifying.read () with
      | None -> readback_at_type ?eta status ctx tm ty
      (* A rigid failure at a singleton type isn't really rigid, since anything else of that type could be used instead. *)
      | Some _ -> (
          try readback_at_type ?eta status ctx tm ty
          with Unsolvable `Rigid when !singleton.test ctx ty -> raise (Unsolvable `Flexible)))

(* Readback is energy-polymorphic: it reads back a value of any energy 's into an ('a, 's) term.  In practice it is only ever called on a *potential* value for display (reading back the forced value of a neutral); in particular, that's the only way a comatch (a no-eta struct) reaches the readback-at-Codata branch.  All other callers read back only kinetic values, with neutral resulting in application spines. *)
and readback_at_type : type mode a z s.
    ?eta:bool ->
    (mode, s) readback_status ->
    (mode, z, a) Ctx.t ->
    (mode, s) value ->
    (mode, kinetic) value ->
    (mode, a, s) term =
 fun ?(eta = false) status ctx tm ty ->
  let view = if Displaying.read () then view_term tm else tm in
  let vty = view_type ty "readback_at" in
  match (vty, view) with
  (* Abstractions (kinetic or potential) are read back uniformly by extending the context using their pi-type. *)
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
          let body =
            readback_eval ~eta (apply_status status filter args) newctx (apply tm filter args)
              output in
          Term.Lam (x, n, filter, body))
  (* If eta-expansion of functions is enabled, we do an eta-expanding readback of any term at a pi-type. *)
  | Canonical (_, Pi { x = name; filter; doms; cods }, ins, tyargs), tm when eta ->
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
  (* At a record type, eta-expansion is controlled by the type's eta and opacity rather than the eta argument passed to readback_at.  We also read back explicit structs (tuples and comatches) here even at non-eta-expanding codatatypes. *)
  | ( Canonical
        (type hmode mn m n)
        (( _,
           Codata
             (type a et)
             ({ eta; opacity; fields = codata_fields; _ } as codata_args :
               (mode, m, n, a, et) codata_args),
           ins,
           _ ) :
          hmode head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      _ ) -> (
      (* The term 'view' has the polymorphic energy 's'.  We also need a uniformly kinetic version of this term; if the energy is kinetic this is the same term, otherwise it is the stored neutral in the potential status. *)
      match
        match (eta, status) with
        | _, Potential neutral -> Some (neutral, (Potential : s energy), (eta : (s, et) eta))
        | Eta, Kinetic -> Some (view, Kinetic, Eta)
        | Noeta, Kinetic -> None
      with
      (* A readback of a kinetic term (necessarily a neutral) at a no-eta codatatype just yields its application spine. *)
      | None -> readback_val ctx tm
      (* In other cases, we might read back a struct. *)
      | Some (ktm, energy, eta) -> (
          let dim = cod_left_ins ins in
          let fldins = ins_zero dim in
          let evaldim = dim_env codata_args.env in
          (* A nontrivially permuted record is not a record type, but we can permute its arguments to find elements of a record type that we can then eta-expand and re-permute. *)
          let ktm, tm, ty, wrap =
            match is_id_ins ins with
            | Some _ -> (ktm, view, ty, fun res -> res)
            | None ->
                let (Perm_to p) = perm_of_ins ins in
                let pinv = deg_of_perm (perm_inv p) in
                let ptm = act_value view pinv (Modalcell.id2 (Ctx.mode ctx)) in
                let pty = act_ty ktm ty pinv (Modalcell.id2 (Ctx.mode ctx)) in
                let pktm : (mode, kinetic) value =
                  match energy with
                  | Kinetic -> ptm
                  | Potential -> act_value ktm pinv (Modalcell.id2 (Ctx.mode ctx)) in
                (pktm, ptm, pty, fun res -> Term.Act (energy, res, deg_of_perm p, (`Other, `Other)))
          in
          let m = cod_left_ins ins in
          let codata_fields =
            Bwd.filter
              (fun (CodatafieldAbwd.Entry
                      (type i)
                      ((_, Codatafield (_, Adjunction { left; _ }, _, _)) :
                        i Field.t * (i, mode * a * D.zero * n * _) Codatafield.t)) ->
                let (Has_filter left_filter) = Modality.filter left m in
                Option.is_some (Modality.filter_is_trivial m left_filter))
              codata_fields in
          match tm with
          (* If the term is a struct, we read back its fields.  Even though this is not technically an eta-expansion, we have to do it here rather than in readback_val because we need the codata type to determine the types at which to read back the fields. *)
          | Struct { fields = comatch_fields; energy; ins = value_ins; eta = _ } -> (
              match D.compare (cod_left_ins value_ins) dim with
              | Neq -> fatal (Anomaly "comatch readback: struct dimension does not match its type")
              | Eq ->
                  let readback_field (Value.StructfieldAbwd.Entry (fld, sf)) :
                      (mode * (_ * _ * s * et)) Term.StructfieldAbwd.entry =
                    match Term.CodatafieldAbwd.find_opt codata_fields fld with
                    (* Lower field *)
                    | Found
                        (Codatafield (_, (Adjunction { left; right; unit; _ } as adj), _, Lower _))
                      ->
                        (* We project the field from the neutral-as-self, keying by the adjunction unit and reading back the component behind the right-adjoint lock. *)
                        let xu = act_value ktm (id_deg D.zero) unit in
                        let tyu = act_ty ktm ty (id_deg D.zero) unit in
                        let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                        (* Build a status and an acted term at energy 's' for energy-polymorphic readback of the body. *)
                        let ((status, sxu) : (_, s) readback_status * (mode, s) value) =
                          match status with
                          | Kinetic -> (Kinetic, xu)
                          | Potential neutral ->
                              let (Val fneu) = field left neutral fld fldins in
                              (Potential fneu, act_value tm (id_deg D.zero) unit) in
                        (* Read back the body term *)
                        let rtm =
                          readback_eval status lctx
                            (field left sxu fld (ins_zero dim))
                            (tyof_field left xu tyu fld (ins_zero evaldim)) in
                        let l =
                          match sf with
                          | Lower (_, _, l) -> l
                          | _ -> `Labeled in
                        Entry (fld, Lower (adj, plus_lock, rtm, l))
                    (* Higher field *)
                    | Found
                        (Codatafield (_, (Adjunction { left; right; unit; _ } as adj), _, Higher _))
                      -> (
                        match Value.StructfieldAbwd.find_opt comatch_fields fld with
                        | Found (Higher (lazy hd)) ->
                            (match Modalcell.compare_adjunction hd.adj adj with
                            | Neq -> fatal (Anomaly "comatch readback: field adjunction mismatch")
                            | Eq -> ());
                            let (Locked (ctx_plus_lock, _)) = Ctx.lock ctx right in
                            (* The self, keyed by the adjunction unit, and its type, exactly as for a lower field. *)
                            let selfnf =
                              {
                                tm = act_value ktm (id_deg D.zero) unit;
                                ty = lazy (act_ty ktm ty (id_deg D.zero) unit);
                              } in
                            let pbm =
                              Term.PlusPbijmap.build dim (Field.dim fld)
                                {
                                  build =
                                    (fun pbij ->
                                      let (Pbij (fldins, fldshuf)) = pbij in
                                      let r = left_shuffle fldshuf in
                                      (* The instance's body lives in the context degenerated by its remaining dimensions, so we build it there, as check_higher_field does: degenerate the context, commute the degeneracy past the right-adjoint lock, and lock the degenerated context to it. *)
                                      let (Degctx (plusmap, dctx, denv)) = degctx ctx r in
                                      let (Shift (plusmap_bg, deg_plus_lock)) =
                                        shift_unplus_lock r plusmap ctx_plus_lock in
                                      let dlctx = Ctx.lock_to dctx right deg_plus_lock in
                                      (* Raise the self into that context, where the remaining dimensions are genuine dimensions and this instance is therefore *projectable*: ins_plus_of_pbij absorbs them into the evaluation dimension, turning the partial bijection into an insertion.  This is the move check_higher_field makes to carry its status into a component.  The body is then just a field projection read back like a lower field's -- the comatch's closure environment never has to be transported, and no shuffleable is needed, since at this dimension nothing remains. *)
                                      let dself = degenerate_normal ctx denv selfnf in
                                      let (Plus rm) = D.plus dim in
                                      let newins = ins_plus_of_pbij fldins fldshuf rm in
                                      let ety =
                                        tyof_field left dself.tm (Lazy.force dself.ty) fld newins
                                      in
                                      let rtm =
                                        readback_at Kinetic dlctx
                                          (field_term left dself.tm fld newins)
                                          ety in
                                      Some (PlusFam.PlusFam (plusmap_bg, Realize rtm)));
                                } in
                            Entry (fld, Higher (adj, ctx_plus_lock, pbm))
                        | _ -> fatal (Anomaly "comatch readback: higher field missing from comatch")
                        )
                    | _ -> fatal (Anomaly "comatch readback: field not found in codata type") in
                  let fields = Bwd.map readback_field comatch_fields in
                  wrap (Term.Struct { eta; dim; fields; energy }))
          (* In addition, if a record type is transparent, or if it's translucent and the term is a tuple in a case tree, and we are reading back for display (rather than for internal typechecking purposes), we do an eta-expanding readback. *)
          | _ -> (
              match eta with
              | Eta -> (
                  match opacity with
                  | (`Transparent l | `Translucent l)
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
                      let fields =
                        Mbwd.map
                          (fun (CodatafieldAbwd.Entry
                                  (type i)
                                  (( fld,
                                     Codatafield
                                       (type f g gmode ag)
                                       ((_, (Adjunction { left; right; unit; _ } as adj), _, Lower _) :
                                         _
                                         * (mode, f, g, gmode) Modalcell.adjunction
                                         * (_, mode, g, gmode, ag) plus_lock
                                         * _) ) :
                                    i Field.t * (i, mode * a * D.zero * n * has_eta) Codatafield.t))
                             ->
                            (* Eta-expansion of a modal field: key the term by the adjunction unit, project, and read back the component in the context locked by the right adjoint (as in the eta-rule for equality). *)
                            let xu = act_value ktm (id_deg D.zero) unit in
                            let tyu = act_ty ktm ty (id_deg D.zero) unit in
                            let (Locked (plus_lock, lctx)) = Ctx.lock ctx right in
                            (* Build a status and an acted term at energy 's' for energy-polymorphic readback of the body. *)
                            let ((status, sxu) : (gmode, s) readback_status * (mode, s) value) =
                              match status with
                              | Kinetic -> (Kinetic, xu)
                              | Potential neutral ->
                                  let (Val fneu) = field left neutral fld fldins in
                                  (Potential fneu, act_value tm (id_deg D.zero) unit) in
                            let rtm =
                              readback_eval status lctx (field left sxu fld fldins)
                                (tyof_field left xu tyu fld fldins) in
                            Term.StructfieldAbwd.Entry
                              (fld, Term.Structfield.Lower (adj, plus_lock, rtm, l)))
                          codata_fields in
                      wrap (Struct { eta = Eta; dim; fields; energy })
                  (* If the term is not a struct and the record type is not transparent/translucent, we pass off to synthesizing readback. *)
                  | _ -> readback_val ctx view)
              | _ -> readback_val ctx view)))
  (* Datatypes are not eta-expanding, but we still need the datatype in order to read back a constructor at that type. *)
  | Canonical (_, Data { constrs; _ }, ins, tyargs), Constr (xconstr, xn, xargs) -> (
      let Eq = eq_of_ins_zero ins in
      (* Pick out the constructor of the datatype that matches the one we're reading back *)
      let (Dataconstr { env; ty = _; fnty }) =
        Abwd.find_opt xconstr constrs <|> Anomaly "constr not found in readback" in
      match D.compare xn (TubeOf.inst tyargs) with
      | Neq -> fatal (Dimension_mismatch ("reading back constrs", xn, TubeOf.inst tyargs))
      | Eq ->
          let (Wrap xargs) = Vec.of_list xargs in
          let lgth = Vec.length xargs in
          (* If a higher-dimensional constructor belongs to a higher version of a datatype, the instantiation arguments of the latter must be lower-dimensional versions of the same constructor.  We extract their arguments to form the boundaries of the types of the arguments of our current constructor. Specifically, tyargs is a tube of normals, each of which is expected to be a lower-dimensional instance of the same constructor, which therefore has a list of modal cubes as arguments.  We want to extract the top element of each of those cubes to form a *list of tubes* of modal values, whereas what we naturally have, after peeling off the constructors, is a *tube of lists*.  We do the conversion with our multiple-output traversal with a variable number of outputs, specifically the length of the telescope. *)
          let tyarg_args =
            find_tyarg_args ~check_dim:"reading back constrs" xconstr lgth tyargs
              ~wrong_arity:(fun () -> Anomaly "inst arg wrong num args in readback at datatype")
              ~wrong_constr:(fun _ -> Anomaly "inst arg wrong constr in readback at datatype")
              ~not_constr:(fun _ -> Anomaly "inst arg not constr in readback at datatype") in
          (* Now xargs and tyarg_args are guaranteed to have the same length, so readback_at_pi doesn't have to worry. *)
          Constr
            ( xconstr,
              dim_env env,
              rigidly @@ fun () ->
              readback_at_pi ctx (dim_env env) (lazy (force_eval_term fnty)) xargs tyarg_args ))
  (* Reading back canonical types themselves (data, codata, record), *at* a universe, happens only for potential terms. *)
  | ( Canonical
        (type hmode m n mn)
        ((_, UU (_, mk), ins0, boundary) :
          hmode head
          * (mode, m, n) canonical
          * (mn, m, n) insertion
          * (D.zero, mn, mn, mode normal) TubeOf.t),
      Canonical { canonical; ins; tyargs; _ } ) -> (
      let (Potential neutral) = status in
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
  (* An indexed datatype that hasn't yet been applied to all of its indices is a canonical type whose type is a pi-type, the remaining indices being still to come, so it isn't caught by the case above.  Such a value is necessarily uninstantiated, since instantiating a datatype before it has all its indices is an anomaly (see apply_unfilled_data_index); thus, unlike the universe case, there is no instantiation to reattach.  The indices supplied so far are restored by readback_data as a potential application spine. *)
  | ( Canonical (_, Pi _, _, _),
      Canonical { canonical = Data ({ indices = Fillvec.Unfilled _; _ } as data_args); tyargs; _ } )
    -> (
      let (Potential _) = status in
      match D.compare_zero (TubeOf.inst tyargs) with
      | Zero -> readback_data ctx data_args
      | Pos _ -> fatal (Anomaly "instantiated datatype is missing indices"))
  | _ -> readback_val ctx tm

(* The synthesizing readback only ever applies to neutrals (a kinetic value).  Any other value reaching it (which can only be a potential value, since other callers pass kinetic neutrals) is an anomaly. *)
and readback_val : type mode a z s. (mode, z, a) Ctx.t -> (mode, s) value -> (mode, a, s) term =
 fun ctx x ->
  match x with
  (* A failed term is read back as Failed, without forcing its value (which would fail). *)
  | Neu { head = Failed _; _ } -> Failed Kinetic
  | Neu { head = Live head; args; value; ty } -> (
      match unfold_solved head value with
      | Some v -> readback_at Kinetic ctx v (Lazy.force ty)
      | None -> (
          match (force_eval value, Displaying.read ()) with
          | Realize v, true -> readback_at Kinetic ctx v (Lazy.force ty)
          | Val (Canonical _), _ ->
              rigidly @@ fun () -> readback_neu ~canonical:`Canonical ctx head args
          (* A neutral that is permanently stuck is rigid, but one that is stuck on a metavariable or might unfold is not, since its arguments might go away. *)
          | Unrealized, _ -> rigidly @@ fun () -> readback_neu ~canonical:`Other ctx head args
          | Blocked b, _ when Option.is_some !blocked_dependence ->
              Reporter.try_with
                ~fatal:(fun d ->
                  match d.message with
                  | No_such_level _ ->
                      Option.iter (fun f -> f b) !blocked_dependence;
                      (Failed Kinetic : (_, _, kinetic) term)
                  | _ -> Reporter.fatal_diagnostic d)
                (fun () -> readback_neu ~canonical:`Other ctx head args)
          | _ -> (
              try readback_neu ~canonical:`Other ctx head args
              with Unsolvable `Rigid -> raise (Unsolvable `Flexible))))
  | Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing readback")
  | Struct _ -> fatal (Anomaly "unexpected struct in synthesizing readback")
  | Constr _ -> fatal (Anomaly "unexpected constr in synthesizing readback")
  | Canonical _ -> fatal (Anomaly "unexpected canonical type in synthesizing readback")

(* A solved unification metavariable is always read back as its solution, since that is what it will become when the term is linked.  This matters because its environment contains its whole context, and thus might use variables that aren't in the context we are reading back in, even if the solution doesn't.  Moreover, when reading back the solution of another unification metavariable (see Unifying), decide whether a neutral with a given head must be unfolded to its value, which is then returned, or whether the readback fails. *)
and unfold_solved : type hmode mode.
    hmode head -> (mode, potential) lazy_eval -> (mode, kinetic) value option =
 fun head value ->
  match Unifying.read () with
  | None -> (
      match head with
      | Meta { meta; kind = Unif_meta unif; _ } when Global.unif_status meta unif <> `Unsolved -> (
          match force_eval value with
          | Realize v -> Some v
          | _ -> None)
      | _ -> None)
  | Some { target = Wrap target; _ } -> (
      let unfold () =
        match force_eval value with
        | Realize v -> Some v
        | _ -> raise (Unsolvable `Flexible) in
      match head with
      | Meta { meta; kind = Unif_meta unif; _ } -> (
          match Meta.compare meta target with
          (* The metavariable being solved can't occur in its solution.  This is rigid if the occurrence is strictly inside a rigid neutral or a constructor, since then the solution would have to be bigger than itself.  But an occurrence at the top of the value, perhaps under lambdas, tuples, or permutations, is not, since for instance the metavariable could be a symmetric square, or equal to its own eta-expansion. *)
          | Eq ->
              raise
                (Unsolvable
                   (if (Option.get (Unifying.read ())).under_rigid then `Rigid else `Flexible))
          | Neq -> (
              match Global.unif_status meta unif with
              | `Unsolved -> None
              | `Speculative | `Written -> unfold ()))
      | Meta { meta; kind = Global_meta; _ }
        when Option.is_some (Meta.sort_of meta) && Meta.origin meta = Origin.Origin.current () ->
          unfold ()
      | _ -> None)

and readback_neu : type hmode mode a z any.
    ?canonical:[ `Canonical | `Other ] ->
    (mode, z, a) Ctx.t ->
    hmode head ->
    (hmode, mode, any, live) apps ->
    (mode, a, kinetic) term =
 fun ?(canonical = `Other) ctx head apps ->
  (* The degeneracies appearing on the spine of a neutral are all *permutations*, which are never displayed with a name like "refl" or "Id" that depends on the sort of their argument.  Thus the only place the sort matters is at the head, where it is computed from the type of the head itself (see readback_head).  Here we only pass along whether the whole neutral is a canonical type, which determines whether a reflexivity at the head is displayed as a superscript. *)
  let sort = (`Other, canonical) in
  match (apps, head) with
  | Emp, _ -> readback_head ~canonical ctx head
  | Snoc (apps, Arg (filter, args, ins)), _ ->
      let modality = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      let (Locked (plus, lctx)) = Ctx.lock ctx modality in
      Term.Act
        ( Kinetic,
          App
            ( Kinetic,
              readback_neu ~canonical ctx head apps,
              cod_left_ins ins,
              filter,
              Modal
                ( modality,
                  plus,
                  CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf lctx tm) } [ args ] ) ),
          p,
          sort )
  | Snoc (apps, Field (filter, fld, fldplus, ins)), _ -> (
      let fm = Modality.filter_modality filter in
      let (To p) = deg_of_ins ins in
      (* The spine inside a modal field projection lives behind a lock by the left adjoint, so we read it back in the locked context, at the filtered dimension. *)
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx fm in
      let t = cod_left_ins ins in
      let inner = readback_neu ~canonical lctx head apps in
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
  | Snoc (Emp, Inst (_, args)), Pi _ when TubeOf.is_full args ->
      (* When reading back a fully instantiated higher-dimensional pi-type, we eta-expand the instantiation arguments so that it can be printed with a nice notation. *)
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ~eta:true ctx x) } [ args ] in
      Inst (Kinetic, readback_head ~canonical ctx head, args)
  | Snoc (apps, Inst (_, args)), _ ->
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ args ] in
      Inst (Kinetic, readback_neu ~canonical ctx head apps, args)

and readback_head : type mode c z.
    ?canonical:[ `Canonical | `Other ] -> (mode, z, c) Ctx.t -> mode head -> (mode, c, kinetic) term
    =
 fun ?(canonical = `Other) ctx h ->
  match h with
  | Var { level; deg; key } -> (
      (* The source of the key is supposed to be the modal annotation of the variable, while its target is supposed to be the composite of all the locks in the context to its right (including any added by the degeneracy).  So we remove its target from the context. *)
      let (Remove_lock (ctx, plus_tgt)) = remove_lock ctx (Modalcell.vtgt key) in
      (* Now we look for the level variable in the remaining context. *)
      let (Lookup
             { result; value; dirt = _; modality; filter; insert; plus = Plus_with_locks (c, _) }) =
        match Ctx.find_level ctx level with
        | Some lookup -> lookup
        (* When reading back the solution of a unification metavariable, a variable not in its context means there is no solution. *)
        | None -> (
            match Unifying.read () with
            | Some { undefined; _ } ->
                raise (Unsolvable (if undefined level then `Flexible else `Rigid))
            | None -> fatal (No_such_level (PLevel level))) in
      (* We check that (1) the modality annotating that variable is the source of the key, and (2) there are no more locks remaining to its right in the context. *)
      match (Modality.compare (Modalcell.vsrc key) modality, result, c) with
      | Eq, `Var (_, fa), Zero -> (
          (* We put the source/annotation modality back onto the context as a lock, as the "Var" term expects. *)
          let (Has_plus_lock plus_src) = plus_lock modality in
          (* If there's a nontrivial degeneracy, we act by it; otherwise we leave it off. *)
          let iplus = plus_with_locks_of_plus_lock plus_src in
          let (Any_deg deg) = renamed_deg value.tm deg in
          let tm =
            match is_id_deg deg with
            | Some _ -> Term.Var (Index (insert, fa, filter, iplus))
            | None ->
                (* The degeneracy acts on the variable itself, so its display name is determined by the sort of the variable's own type. *)
                let sort = sort_of_val (Modality.src modality) (Lazy.force value.ty) in
                Act (Kinetic, Term.Var (Index (insert, fa, filter, iplus)), deg, (sort, canonical))
          in
          (* And if the key is nontrivial, we act by it; otherwise we leave it off. *)
          match (Modality.compare_id modality, plus_src, plus_tgt) with
          | Eq, Plus_lock (Zero _, Zero), Plus_with_locks (Zero, Zero _) -> tm
          | _ -> Key { tm; cell = key; plus_tgt; plus_src })
      (* When reading back the solution of a unification metavariable, the variable might have been found in the wrong modal position in the metavariable's context, which means there is no solution. *)
      | Neq, _, _ when Option.is_some (Unifying.read ()) -> raise (Unsolvable `Flexible)
      | _, _, Suc _ when Option.is_some (Unifying.read ()) -> raise (Unsolvable `Flexible)
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
      | None ->
          (* Likewise, a degeneracy acting on a constant is displayed according to the sort of the constant's own type, and according to whether that constant is (a family of) canonical types. *)
          let sort =
            Reporter.discard_errors ~fallback:(fun () -> `Other) @@ fun () ->
            let (Definition { mode; ty; _ }) = Global.find_const name in
            sort_of_val mode (eval_term (Emp (mode, D.zero)) ty) in
          let canonical =
            match is_canonical_const name with
            | `Canonical -> `Canonical
            | `Other -> canonical in
          Act (Kinetic, Const name, deg, (sort, canonical)))
  | Meta { meta; kind; env; ins } -> (
      let ty = Global.meta_ty meta kind in
      let with_perm (tm : (mode, c, kinetic) term) : (mode, c, kinetic) term =
        match is_id_ins ins with
        | Some _ -> tm
        | None ->
            (* A degeneracy on a metavariable with a zero-dimensional environment is always a permutation, whose display doesn't depend on the sort. *)
            let (To perm) = deg_of_ins ins in
            Act (Kinetic, tm, perm, (`Other, canonical)) in
      (* We only need the context of the metavariable if we have to bind its variables, which may be expensive to compute for a unification metavariable, so we don't ask for it otherwise. *)
      let letonly () =
        let termctx = Global.meta_termctx meta kind in
        Letonly { termctx; env = readback_env ctx env termctx; tm = Meta (meta, kind, Kinetic); ty }
      in
      (* If the environment is the identity, possibly weakened, we can omit it. *)
      match readback_meta_at_idenv ctx meta kind env with
      | Some tm -> with_perm tm
      | None -> (
          match no_checked_vars (Meta.tctx meta) with
          (* If the context of the metavariable has no variables, an environment for it of positive dimension carries no information, so the metavariable is just degenerated, possibly with a permutation. *)
          | Some Eq -> (
              match readback_meta_at_idenv ctx meta kind (Emp (Ctx.mode ctx, D.zero)) with
              | Some tm -> (
                  let (To perm) = deg_of_ins ins in
                  let (DegExt (_, _, deg)) = comp_deg_extending (deg_zero (cod_left_ins ins)) perm in
                  match is_id_deg deg with
                  | Some _ -> tm
                  | None -> Act (Kinetic, tm, deg, (`Other, canonical)))
              | None -> with_perm (letonly ()))
          (* Otherwise, we bind the variables of the metavariable's context with a let-only. *)
          | None -> with_perm (letonly ())))
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
    Cod (kfilter, readback_val sctx (apply_binder_term b kfilter sargs)) in
  Term.Pi
    {
      x;
      filter;
      doms =
        Modal
          (modality, plus, CubeOf.mmap { map = (fun _ [ dom ] -> readback_val lctx dom) } [ doms ]);
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
  | Ext (envctx, ({ plus_lock = dplus; bindings; filter = filtered; _ } as entry), _, comp) -> (
      match ext_kind entry comp with
      (* An alias contributes nothing to the environment, so we skip it. *)
      | Ext_alias -> readback_ordered_env ctx env envctx
      | Ext_dim ->
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
          (* We also analogously lock the environment we're reading back, for purposes of evaluating types. *)
          let lenv = lock_env aenv dplus in
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
  | Lock (envctx, g) ->
      (* We strip off the corresponding Lock from the environment being read back, along with any prekeys on top of it. *)
      let (Restrict_keys (env, pre)) =
        restrict_keys env (plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g) in
      if Modalcell.is_id pre then
        (* If there is no prekey action, we just remove the lock from the context we're reading back *into*, and read back the residual environment as a locked term environment. *)
        let (Remove_lock (ctx, plus_tgt)) = remove_lock ctx (Modality.of_gen g) in
        Term.Lock { env = readback_ordered_env ctx env envctx; gen = g; plus_tgt }
      else
        (* A prekey action mediates between a context locked by its vertical source (where the keyed value was created, e.g. behind a key or a parametric locker's locks) and one locked by its vertical target (the actual ambient context, e.g. after the locker's counit discharged those locks).  So before removing the lock, we remove the target of the prekey from the context and re-lock it with the prekey's source, recording both in the term-level Prekey. *)
        let (Remove_lock (ctx, pre_tgt)) = remove_lock ctx (Modalcell.vtgt pre) in
        let (Locked (pre_src, ctx)) = Ctx.lock ctx (Modalcell.vsrc pre) in
        let (Remove_lock (ctx, plus_tgt)) = remove_lock ctx (Modality.of_gen g) in
        Prekey
          {
            env = Term.Lock { env = readback_ordered_env ctx env envctx; gen = g; plus_tgt };
            cell = pre;
            plus_src = pre_src;
            plus_tgt = pre_tgt;
          }

(* Read back a context of values into a context of terms. *)

(* Read back the bindings in the last entry of a context, which live in the whole context locked by the modality of the entry.  Each value or type in the cube of bindings can refer to the variables that come before it in the cube (which include its faces), but not to itself or those that come after it.  So we read them back in the context to the left of the entry extended by delayed copies of its bindings, which can't be found until they are forced, and we force each one after reading back its value and type.  In particular, this prevents a variable let-bound to a metavariable from being read back as itself while reading back its own value (see let_var_of_meta). *)
and readback_entry : type mode a x ax b bb b2 dom modality n.
    (mode, a, b) Ctx.Ordered.t ->
    (dom, modality, mode, x, n, b2) Ctx.entry ->
    (a, x, ax) N.plus ->
    (mode, b2, mode, b, unit, bb) Tctx.comp ->
    (mode, ax, bb, modality, dom, n) readback_entry =
 fun rest { bindings; filter; vis } ax comp ->
  let modality = Modality.filter_modality filter in
  let delayed = CubeOf.mmap { map = (fun _ [ b ] -> Binding.delay b) } [ bindings ] in
  let ctx = Ctx.of_ordered (Snoc (rest, { bindings = delayed; filter; vis }, ax, comp)) in
  let (Locked (plus_lock, lctx)) = Ctx.lock ctx modality in
  let bindings =
    CubeOf.mmap
      {
        map =
          (fun _ [ b; d ] ->
            let nf = Binding.value b in
            let ty = readback_val lctx (Lazy.force nf.ty) in
            let tm =
              match Binding.level b with
              | Some _ -> None
              | None -> Some (readback_nf lctx nf) in
            Binding.force d;
            ({ tm; ty } : (dom, _) binding));
      }
      [ bindings; delayed ] in
  Readback_entry (plus_lock, lctx, bindings)

and readback_ordered_ctx : type mode a b. (mode, a, b) Ctx.Ordered.t -> (mode, a, b) ordered_termctx
    = function
  | Emp mode -> Emp mode
  | Snoc (rest, ({ bindings; filter; vis } as entry), af, comp) -> (
      let top = Binding.value (CubeOf.find_top bindings) in
      let (Readback_entry (plus_lock, lctx, bindings)) = readback_entry rest entry af comp in
      let rest = readback_ordered_ctx rest in
      match vis with
      | Vis (kind, { dim; plusdim; vars; hasfields; fields; fplus }) ->
          (* Fields as illusory variables are only used when typechecking records, which have substitution dimension 0 and can have no higher fields, so as field insertion we can use the identity on zero. *)
          let idm = Modality.id (Ctx.mode lctx) in
          let fins = ins_zero D.zero in
          let fields =
            Bwv.map
              (fun (f, x, _) ->
                let fldty = readback_val lctx (tyof_field idm top.tm (Lazy.force top.ty) f fins) in
                (f, x, fldty))
              fields in
          let vis = Vis (kind, { dim; plusdim; vars; hasfields; fields; fplus }) in
          Ext (rest, { plus_lock; bindings; filter; vis }, af, comp)
      | Invis ->
          (* Invisible variables are anonymous, but we can still record display hints from their types, since after readback the types are terms and the hints can no longer be computed on demand.  Since this only affects display, if anything goes wrong computing the type we just skip the hints (though internal errors are still reported). *)
          let hints =
            Reporter.discard_errors ~fallback:(fun () -> no_hints) @@ fun () ->
            View.hints_of_ty (Lazy.force top.ty) in
          Ext (rest, { plus_lock; bindings; filter; vis = Invis { hints } }, af, comp))
  | Lock (ctx, lock) -> Lock (readback_ordered_ctx ctx, lock)
  | Weaken (ctx, code) -> Weaken (readback_ordered_ctx ctx, code)

and readback_ctx : type mode a b. (mode, a, b) Ctx.t -> (mode, a, b) termctx = function
  | Permute { perm; ctx; _ } -> Permute (perm, readback_ordered_ctx ctx)

(* Now we move on to readback of potential-only values like data, codata, match, and comatch. *)

(* ********** Readback of data types (for display only) ********** *)

(* Read back a datatype definition. *)
and readback_data : type mode a b m j ij.
    (mode, a, b) Ctx.t -> (mode, m, j, ij) Value.data_args -> (mode, b, potential) term =
 fun ctx { constrs; recursive; tyfam; hints; dim; indices } ->
  let ij = Fillvec.expected_length indices in
  (* Evaluate each constructor's stored function-type in its appropriately-dimensional environment and then read it back. *)
  let constrs = Abwd.mapi (readback_dataconstr ctx) constrs in
  let tyfam = readback_nf ctx (nf_of_neu (force_eval_term tyfam) "readback_data") in
  let data : (mode, b, potential) term =
    Canonical (Data { indices = ij; evaldim = dim; constrs; recursive; tyfam; hints }) in
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
 fun ctx c (Dataconstr { env; ty; fnty = _ }) ->
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
  readback_val ctx (Norm.inst ft boundary)

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
    (mode, a, b) Ctx.t -> (mode, r, b) env -> mode normal -> mode normal =
 fun ctx degenv nf ->
  let ctm = readback_nf ctx nf in
  let cty = readback_val ctx (Lazy.force nf.ty) in
  { tm = eval_term degenv ctm; ty = lazy (type_of_eval degenv ctm cty) }

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
     (Entry
        (type i)
        ((fld, Codatafield (self, (Adjunction { left; right; unit; _ } as adj), fld_plus_lock, cf)) :
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
               tyof_lower_codatafield (val_of_norm_cube selfnfs) (TubeOf.boundary selfnfs) fld adj
                 fld_plus_lock fldty codataenv evaldim cm_cn ~key:`Nokey in
             let ty = readback_val sctx ety in
             Entry (fld, Codatafield (self, adj, plus_lock, Lower ty))
         | Higher (fldtermctx, fldtys) ->
             (* A codatatype with a higher field has intrinsic dimension zero, so its whole dimension, at which the self-variable cube lives and at which the instances of the field are indexed, is its evaluation dimension. *)
             let Eq = D.plus_uniq cm_cn (D.plus_zero evaldim) in
             let tys =
               readback_higher_codatafield ctx codataenv fld_plus_lock fldtermctx fldtys
                 (CubeOf.dim selfnfs) fld adj selfnfs sctx in
             Entry (fld, Codatafield (self, adj, plus_lock, Higher (readback_ctx lctx, tys))))

(* Read back the instances of one higher field of a codatatype value being displayed, as the pbijmap of types that Codatafield.Higher stores: one entry per partial bijection between the codatatype's evaluation dimension m and the field's intrinsic dimension i.  The self variable, its cube, and the context they live in are those built by readback_codata, while the environment, lock, termctx and stored types are those of the codatatype value being displayed; the ambient context is needed only to degenerate for a non-projectable instance. *)
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
          (Pbij (fldins, fldshuf) : (m, i, r) pbij)
          :
          (r, gmode * (bg, (f, m) dim_entry) snoc) Term.FieldtypeFam.t
        ->
          match D.compare_zero (left_shuffle fldshuf) with
          | Zero ->
              (* Projectable instance: read back in the locked, self-extended context, as for a lower field, with a trivial degeneration and hence no remaining dimensions for the self cube to be degenerated by.  As there, we display the type as it was *declared*, computed from the codatatype's own environment and left un-keyed (~key:`Nokey). *)
              let Eq = eq_of_zero_shuffle fldshuf in
              let ety =
                tyof_higher_codatafield (val_of_norm_cube selfnfs) (TubeOf.boundary selfnfs)
                  (D.zero_plus m) fld adj codataenv fldins ~shuf:Trivial plus_lock fldtermctx ic0
                  fldty ~key:`Nokey in
              Fieldtype (Plusmap.zerol (Ctx.tctx sctx), readback_val sctx ety)
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
                        eval_env (lock_env degenv plus) r_k (readback_env lctx e tctx));
                  } in
              let (Locked (fplus, flctx)) = Ctx.lock sctx left in
              let fdegenv = lock_env sdegenv fplus in
              let (Plus r_m) = D.plus m in
              let values =
                degenerate_value_cube flctx fdegenv r_m
                  (CubeOf.mmap { map = (fun _ [ nf ] -> nf.tm) } [ selfnfs ]) in
              let tyargs =
                TubeOf.mmap
                  { map = (fun _ [ nf ] -> degenerate_normal flctx fdegenv nf) }
                  [ TubeOf.boundary selfnfs ] in
              let ety =
                tyof_higher_codatafield values tyargs r_m fld adj codataenv fldins ~shuf plus_lock
                  fldtermctx ic0 fldty ~key:`Nokey in
              Fieldtype (plusmap, readback_val dsctx ety));
    }

(* Read back a codatatype value whose insertion is *not* the identity, where a Gel-dimension has been permuted with evaluation dimensions.  Such a value is no longer a record type at all: its fields can't be projected, and there is no self-variable cube in the order in which the fields were declared.  But it is the permutation of a value that is one, so we un-permute it, read that back as a codatatype, and apply the permutation to the result as a degeneracy.  If it is instantiated, we first un-instantiate entirely, then re-instantiate afterwards.  Because a permuted codatatype is not a codatatype, we can't push the permutation or instantiation arguments inside the field types. *)
and readback_permuted_codata : type mode a b m k mk e n.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (m, k, mk, mode normal) TubeOf.t ->
    (mk, e, n) insertion ->
    (mode, b, potential) term =
 fun ctx neutral tyargs ins ->
  let mode = Ctx.mode ctx in
  match D.compare_zero (TubeOf.inst tyargs) with
  | Pos _ ->
      let uninst = uninstantiate mode neutral in
      Inst
        ( Potential,
          readback_permuted_codata ctx uninst.tm (TubeOf.empty (TubeOf.out tyargs)) ins,
          TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ tyargs ] )
  | Zero -> (
      let (Perm_to p) = perm_of_ins ins in
      let pinv = deg_of_perm (perm_inv p) in
      match act_value neutral pinv (Modalcell.id2 mode) with
      | Neu { value; ty = pty; _ } as pneutral -> (
          (* We basically go back to the Canonical case of readback_at. *)
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
              | Neq, _ ->
                  fatal
                    (Dimension_mismatch ("readback_permuted_codata", TubeOf.uninst ptyargs, pmk))
              | _, None ->
                  fatal
                    (Anomaly "readback_permuted_codata: unpermuted insertion is not the identity"))
          | _ -> fatal (Anomaly "readback_permuted_codata: unpermuted value has wrong shape"))
      | _ -> fatal (Anomaly "readback_permuted_codata: unpermuted value is not a neutral"))

(* Un-instantiate a type value: strip the instantiation off the end of its neutral spine, and off its canonical value, returning the whole-dimensional type that was instantiated, as a normal.  A value carrying no instantiation is returned unchanged, which is what bottoms out the recursion below.  The uninstantiated type's own type is not stored anywhere -- inst computes the instantiated type from it and keeps only the spine -- so we rebuild it: a universe of the whole dimension, instantiated at the uninstantiated type's boundary.  That boundary is exactly what we are stripping off, in the two halves that a full tube splits into: its outer part is the *types* of the instantiation arguments, and its inner part (empty unless the instantiation was partial) is the arguments of the universe that the instantiated type itself belongs to.  Both arrive instantiated in their turn -- what we have of the boundary of "(Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,)" is "Gel A B R a₀ b₀" and "Id A a₀ a₁", where we want "Gel A B R" and "Id A" -- so we un-instantiate them recursively.  The recursion is on dimension, since each of them is lower-dimensional than the whole. *)
and uninstantiate : type mode. mode Mode.t -> (mode, kinetic) value -> mode normal =
 fun mode ty ->
  match view_term ty with
  | Neu { head; args = Snoc (base_args, Inst (_, insargs)); value; ty = instty } -> (
      match view_type (Lazy.force instty) "uninstantiate" with
      | Canonical (_, UU (_, umk), uins, uargs) -> (
          let Eq = eq_of_ins_zero uins in
          (* The universe the instantiated type belongs to has exactly its uninstantiated dimensions. *)
          match D.compare umk (TubeOf.uninst insargs) with
          | Neq -> fatal (Dimension_mismatch ("uninstantiate", umk, TubeOf.uninst insargs))
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

(* The "about" command reads back the *potential* value of a neutral, passing the neutral itself as readback's status so that a canonical type displays as its declaration and a comatch as itself; readback_at handles the rest, including descending through parameter abstractions.  None means the neutral has no potential value at all to display -- an axiom, or a permanently stuck case tree -- so the caller shows its normal form instead. *)
let rec readback_about : type mode a b.
    (mode, a, b) Ctx.t -> (mode, kinetic) Value.value -> (mode, b, potential) Term.term option =
 fun ctx value ->
  match value with
  | Neu { value = v; ty; _ } -> (
      match force_eval v with
      | Val v -> Some (readback_at (Potential value) ctx v (Lazy.force ty))
      (* Under glued evaluation, a constant whose definition is an ordinary term rather than a case tree is a neutral whose value realizes that term.  It has no potential value of its own, but the neutral it realizes to may, so we look there. *)
      | Realize v -> readback_about ctx v
      | Unrealized | Blocked _ -> None)
  | _ -> None

(* ********** Solutions of unification metavariables ********** *)

(* A unification metavariable with context mctx, occurring with a zero-dimensional environment menv in a context cctx, can be solved easily if menv is a *renaming*: it sends the free variables of mctx to plain variables of cctx.  Then we don't need to compute an inverse substitution: a context that has the same shape as mctx, but in which each variable has the level of the variable of cctx that menv sends it to, already acts as that inverse.  Reading back a value of cctx in such a context finds each variable in menv's image by its level, producing a term in mctx, and fails if it encounters any other variable (see Readback.Unifying).

   The renaming need not be injective, nor preserve modal annotations.  A variable of cctx that is the image of more than one variable of mctx, or of a variable with a different annotation, is "undefined": it has no inverse, so if the value contains it we fail.  But if the value doesn't contain it, then the resulting solution is most general.  This is because substituting variables for variables can't trigger any computation, so if some solution of the metavariable used a variable of mctx sent to such a variable, then the value would contain that variable too.  (This argument doesn't apply if the image is not a plain variable, so in that case we don't have a renaming at all.)

   The image of a variable can also be a permutation of a plain variable.  Since permutations are invertible, and a permutation of a variable is still neutral, this is no different: the corresponding variable of mctx has that permuted variable as its value, and readback inverts the permutation when it finds that variable (see renamed_deg).

   The metavariable can also be applied to arguments, as long as they are also plain variables or permutations of them.  We treat these like further entries of its environment, so that the renamed context extends it by one entry for each argument (whose types we don't need to know, since they are only for readback), and the solution is then an abstraction over them.

   We prefer eta-short solutions, so if the value being compared with the metavariable ends with some of the same arguments, we first try to omit them from both, since a solution of ?f =? g is also one of ?f y =? g y.  We only do this if nothing is undefined, since otherwise we could change the problem: ?f x x =? g x has no most general solution, but ?f x =? g does.

   A variable of mctx sent to an undefined variable can't be used in the solution.  But this is not enough to make the solution well-typed: the type of another variable of mctx, or of the metavariable, might depend on it.  Thus we also treat any variable whose type contains an undefined variable as undefined itself, and the caller must check that the type of the metavariable doesn't contain one either.  Since menv is a renaming, it suffices to read back the types obtained by substitution with menv, which we already have. *)
type (_, _) renamed_ctx =
  | Renamed_ctx : {
      ctx : ('mode, 'a, 'bc) Ctx.t;
      check_type : bool;
      (* Whether a level of the current context is in the image of the renaming, though possibly undefined. *)
      in_image : level -> bool;
      wrap : ('mode, 'bc, kinetic) term -> ('mode, 'b, kinetic) term;
      contracted : (unit -> ('mode, 'b, kinetic) term option) list;
    }
      -> ('mode, 'b) renamed_ctx

type (_, _) renamed_ordered =
  | Renamed_ordered : ('mode, 'a, 'b) Ctx.Ordered.t -> ('mode, 'b) renamed_ordered

(* A value in an environment that is a permutation of a plain variable, and whether it has the annotation of the corresponding variable in the metavariable's context. *)
type 'mode renamed_var = { var : level; deg : any_deg; normal : 'mode normal; annotated : bool }

exception Not_renaming

let renamed_var : type dom modality mode.
    (dom, modality, mode) Modality.t -> (dom, kinetic) value -> dom renamed_var =
 fun modality v ->
  match view_term v with
  | Neu { head = Live (Var { level; deg; key }); args = Emp; ty; _ } as tm -> (
      match (perm_of_deg deg, Modalcell.is_id key) with
      | Some _, true ->
          let annotated =
            match Modality.compare (Modalcell.vsrc key) modality with
            | Eq -> true
            | Neq -> false in
          { var = level; deg = Any_deg deg; normal = { tm; ty }; annotated }
      | _ -> raise_notrace Not_renaming)
  | _ -> raise_notrace Not_renaming

(* An application spine consisting only of function arguments has the same mode at both ends. *)
let rec arg_spine : type hmode mode any. (hmode, mode, any, live) apps -> (hmode, mode) Eq.t option
    = function
  | Emp -> Some Eq
  | Snoc (args, Arg _) -> arg_spine args
  | Snoc (_, Field _) | Snoc (_, Inst _) -> None

(* The result of extending a renamed context by the arguments of a metavariable, including the type of the metavariable applied to those arguments, if known. *)
type (_, _) renamed_args =
  | Renamed_args :
      ('mode, 'a, 'bc) Ctx.Ordered.t
      * (('mode, 'bc, kinetic) term -> ('mode, 'b, kinetic) term)
      * ('mode, kinetic) value option
      -> ('mode, 'b) renamed_args

(* The head and a prefix of the spine of a neutral value that could be an eta-contracted solution of a metavariable applied to arguments. *)
type _ contractible =
  | Contractible : 'hmode head * ('hmode, 'mode, 'any, live) apps -> 'mode contractible

(* A prefix of a neutral doesn't have a stored value, so we can only contract neutrals whose readback doesn't need to look at it (see unfold_solved). *)
let contractible : type mode. (mode, kinetic) value -> mode contractible option = function
  | Neu { head = Live (Var _ as head); args; _ } -> Some (Contractible (head, args))
  | Neu { head = Live (Const _ as head); args; _ } -> Some (Contractible (head, args))
  | Neu { head = Live (Meta { meta; kind = Unif_meta unif; _ } as head); args; _ }
    when Global.unif_status meta unif = `Unsolved -> Some (Contractible (head, args))
  | _ -> None

(* Whether a value is literally the variable with a given level and degeneracy, with no key or arguments. *)
let is_var_with_deg : type mode s m n. level -> (m, n) deg -> (mode, s) value -> bool =
 fun var deg x ->
  match x with
  | Neu { head = Live (Var { level; deg = xdeg; key }); args = Emp; _ } ->
      level = var && Modalcell.is_id key && Option.is_some (deg_equiv deg xdeg)
  | _ -> false

(* Whether an argument of a metavariable, which is a cube of permutations of plain variables, is the same as the last argument of another neutral. *)
let same_arg : type dom1 modality1 n1 m1 dom2 modality2 n2 m2 mode x1 y1 x2 y2.
    (dom1, modality1, mode, n1, m1) Modality.filter_dim ->
    (n1, dom1 normal) CubeOf.t ->
    (x1, m1, y1) insertion ->
    (dom2, modality2, mode, n2, m2) Modality.filter_dim ->
    (n2, dom2 normal) CubeOf.t ->
    (x2, m2, y2) insertion ->
    bool =
 fun filter1 xs1 ins1 filter2 xs2 ins2 ->
  let modality1 = Modality.filter_modality filter1 in
  match
    ( Modality.compare modality1 (Modality.filter_modality filter2),
      D.compare (CubeOf.dim xs1) (CubeOf.dim xs2),
      D.compare (cod_left_ins ins1) (cod_left_ins ins2),
      is_id_ins ins2 )
  with
  | Eq, Eq, Eq, Some _ ->
      let same = ref true in
      CubeOf.miter2
        {
          it2 =
            (fun _ (x1 : _ normal) (x2 : _ normal) ->
              let { var; deg = Any_deg deg; _ } = renamed_var modality1 x1.tm in
              if not (is_var_with_deg var deg (view_term x2.tm)) then same := false);
        }
        xs1 xs2;
      !same
  | _ -> false

(* Determine the variables to use for abstracting over an argument of a metavariable, from the function-type of the metavariable if we can, and also the codomain of that function-type applied to the argument.  This is only for display, so if anything goes wrong we just use anonymous variables. *)
let renamed_binder : type dom modality mode n m.
    (mode, kinetic) value option ->
    (dom, modality, mode, n, m) Modality.filter_dim ->
    m D.t ->
    (n, dom normal) CubeOf.t ->
    n variables * (mode, kinetic) value option =
 fun ty filter m xs ->
  let anon () = (singleton_variables (CubeOf.dim xs) (`Anon no_hints), None) in
  match ty with
  | None -> anon ()
  | Some ty -> (
      Reporter.discard_errors ~fallback:anon @@ fun () ->
      match view_type ~severity:Asai.Diagnostic.Error ty "renamed_binder" with
      | Canonical (_, Pi { x; filter = pifilter; doms; cods }, ins, tyargs) -> (
          let Eq = eq_of_ins_zero ins in
          match
            ( Modality.compare (Modality.filter_modality filter) (Modality.filter_modality pifilter),
              D.compare m (BindCube.dim cods) )
          with
          | Eq, Eq ->
              let Eq = Modality.filter_uniq filter pifilter in
              (View.fill_hints doms x, Some (tyof_app cods tyargs filter (val_of_norm_cube xs)))
          | _ -> anon ())
      | _ -> anon ())

(* Look up the cube of values of a cube of variables in an environment. *)
let renamed_values : type dom modality mode b k.
    (mode, D.zero, (b, (modality, k) dim_entry) snoc) env ->
    (dom, modality, mode) Modality.t ->
    k D.t ->
    (k, (dom, kinetic) value) CubeOf.t =
 fun env modality k ->
  let (Looked_up { act; op; entry = xs; pre }) =
    lookup_cube env (D.zero_plus k) modality modality Now (id_opt_op k) in
  match (is_id_opt_op op, Modalcell.is_id pre) with
  | Some Eq, true ->
      let s = id_deg k in
      CubeOf.build k { build = (fun fa -> act (CubeOf.find xs fa) s pre) }
  | _ -> raise_notrace Not_renaming

(* Given a metavariable, the current context, the metavariable's environment, arguments, type, and context, and the value being compared with it, compute the renamed context, along with whether anything is undefined in it, a function wrapping a term in that context in abstractions over the arguments, and a list of eta-contracted solutions to try first, most contracted first; or return None if the environment and arguments aren't a renaming.  Since the entries of the new context have values and types in the current context, and all the levels of its variables are levels of the current context, new variables created in it are given levels above those of the current context. *)
let renamed_ctx : type mode a b c d n x any.
    (mode, x, d, kinetic) Meta.t ->
    (mode, a, b) Ctx.t ->
    (mode, n, d) env ->
    (mode, mode, any, live) apps ->
    (mode, d, kinetic) term ->
    (mode, c, d) Ctx.t ->
    (mode, kinetic) value ->
    (mode, d) renamed_ctx option =
 fun meta ctx env args mty (Permute { ctx = mctx; _ }) v ->
  let level = Ctx.level ctx in
  let counts : (level, int) Hashtbl.t = Hashtbl.create 20 in
  let undefined = ref false in
  let count_var : type dom modality mode.
      (dom, modality, mode) Modality.t -> (dom, kinetic) value -> unit =
   fun modality v ->
    let { var; annotated; _ } = renamed_var modality v in
    let count = Option.value (Hashtbl.find_opt counts var) ~default:0 in
    Hashtbl.replace counts var (count + 1);
    if count > 0 || not annotated then undefined := true in
  (* First we make a pass through the environment and arguments to check that they are a renaming and find out which variables are repeated, since the variables in the context we build have to be determined starting from the left. *)
  let rec scan : type mode a d. (mode, a, d) Ctx.Ordered.t -> (mode, D.zero, d) env -> unit =
   fun mctx env ->
    match mctx with
    | Emp _ -> ()
    | Weaken (mctx, _) -> scan mctx env
    | Lock (mctx, g) ->
        let (Restrict_keys (env, pre)) =
          restrict_keys env (plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g) in
        (* A nonidentity prekey encountered in the environment, such as the counit of an adjunction after projecting a modal field, means that we can't invert the variables behind this lock, since their keys would have to be transposed along that prekey.  In the context we build, readback will fail on them anyway, since it won't find the locks it needs.  So we can only allow values that don't use them, and treat this like having undefined variables. *)
        if not (Modalcell.is_id pre) then undefined := true;
        scan mctx env
    | Snoc (mctx, entry, _, comp) -> (
        match Ctx.Ordered.ext_kind entry comp with
        | Ext_alias -> scan mctx env
        | Ext_dim ->
            let modality = Ctx.modality_entry entry in
            let bindings = Ctx.bindings_entry entry in
            CubeOf.miter2
              {
                it2 =
                  (fun _ v b ->
                    (* A let-bound variable isn't part of the renaming: its value in the environment is determined by the rest of the environment. *)
                    if Option.is_some (Binding.level b) then count_var modality v);
              }
              (renamed_values env modality (CubeOf.dim bindings))
              bindings;
            scan mctx (remove_top env)) in
  let rec scan_args : type any. (mode, mode, any, live) apps -> unit = function
    | Emp -> ()
    | Snoc (args, Arg (filter, xs, ins)) ->
        (* A degeneracy on the application isn't part of a renaming. *)
        if Option.is_none (is_id_ins ins) then raise_notrace Not_renaming;
        scan_args args;
        let modality = Modality.filter_modality filter in
        CubeOf.miter { it = (fun _ [ (x : _ normal) ] -> count_var modality x.tm) } [ xs ]
    | Snoc (_, Field _) | Snoc (_, Inst _) -> raise_notrace Not_renaming in
  (* Then we build the context from the left.  The bindings of a cube of variables are determined by the values in the environment, except that a let-bound variable has no level for readback to find.  The types of the variables in a cube can depend on the earlier ones, so we fill them in as we go.  We read back those types in the context locked by the modality of the variables. *)
  let renamed_bindings : type dom modality mode a b k.
      (mode, a, b) Ctx.Ordered.t ->
      (dom, modality, mode, k, k) Modality.filter_dim ->
      (k, (dom, kinetic) value) CubeOf.t ->
      (k, bool) CubeOf.t ->
      (k, dom Binding.t) CubeOf.t =
   fun rest filter values free ->
    let modality = Modality.filter_modality filter in
    let vbs = CubeOf.build (CubeOf.dim values) { build = (fun _ -> Binding.unknown ()) } in
    let (Locked (_, lctx)) = Ctx.Ordered.lock (Ctx.Ordered.invis rest filter vbs) modality in
    let tyctx = Ctx.of_ordered ~level lctx in
    let dom = Modality.src modality in
    CubeOf.miter2
      {
        it2 =
          (fun fa v vb ->
            if CubeOf.find free fa then
              let { var; normal; annotated; _ } = renamed_var modality v in
              let defined =
                Hashtbl.find_opt counts var = Some 1
                && annotated
                && ((not !undefined)
                   ||
                     try
                       let _ = readback_val tyctx (Lazy.force normal.ty) in
                       true
                     with Unsolvable _ -> false) in
              if defined then Binding.specify vb (Some var) normal
              else
                (* An undefined variable gets a failed value, rather than the one in the environment, so that it won't be recognized as part of an identity environment of some other metavariable. *)
                Binding.specify vb None
                  { tm = failed dom (lazy (failed_type dom)); ty = lazy (failed_type dom) }
            else
              (* Nothing ever looks at the type of the binding of a let-bound variable. *)
              Binding.specify vb None
                {
                  tm = v;
                  ty = lazy (fatal (Anomaly "type of let-bound variable in renamed context"));
                });
      }
      values vbs;
    vbs in
  (* Aliases and weakening entries contribute nothing to the checked length, the environment, or readback, so we omit them. *)
  let rec go : type mode a d.
      (mode, a, d) Ctx.Ordered.t -> (mode, D.zero, d) env -> (mode, d) renamed_ordered =
   fun mctx env ->
    match mctx with
    | Emp mode -> Renamed_ordered (Emp mode)
    | Weaken (mctx, _) -> go mctx env
    | Lock (mctx, g) ->
        let (Restrict_keys (env, _)) =
          restrict_keys env (plus_with_locks_lock (plus_with_no_locks (Modality.Gen.tgt g)) g) in
        let (Renamed_ordered mctx) = go mctx env in
        Renamed_ordered (Lock (mctx, g))
    | Snoc (mctx, entry, af, comp) -> (
        match Ctx.Ordered.ext_kind entry comp with
        | Ext_alias -> go mctx env
        | Ext_dim ->
            let modality = Ctx.modality_entry entry in
            let bindings = Ctx.bindings_entry entry in
            let k = CubeOf.dim bindings in
            let values = renamed_values env modality k in
            let (Renamed_ordered rest) = go mctx (remove_top env) in
            let free =
              CubeOf.build k
                { build = (fun fa -> Option.is_some (Binding.level (CubeOf.find bindings fa))) }
            in
            let vbs = renamed_bindings rest (Ctx.filter_entry entry) values free in
            let (Plus a_x) = N.plus (N.plus_right af) in
            Renamed_ordered (Snoc (rest, { entry with bindings = vbs }, a_x, comp))) in
  let contracted : (unit -> (mode, d, kinetic) term option) list ref = ref [] in
  let rec go_args : type a any.
      (mode, a, d) Ctx.Ordered.t ->
      (mode, mode, any, live) apps ->
      (mode, kinetic) value option ->
      mode contractible option ->
      (mode, d) renamed_args =
   fun rest args ty vspine ->
    match args with
    | Emp -> Renamed_args (rest, (fun tm -> tm), ty)
    | Snoc (args, Arg (filter, xs, ins)) ->
        (* If the last arguments agree, we can continue to compare the rest of the arguments and try to omit this one. *)
        let vprefix : mode contractible option =
          match vspine with
          | Some (Contractible (head, Snoc (vargs, Arg (vfilter, ys, vins))))
            when same_arg filter xs ins vfilter ys vins -> Some (Contractible (head, vargs))
          | _ -> None in
        let (Renamed_args (rest, wrap, ty)) = go_args rest args ty vprefix in
        (match vprefix with
        | Some (Contractible (head, vargs)) ->
            let rctx = Ctx.of_ordered ~level rest in
            let attempt () =
              Displaying.run ~env:false @@ fun () ->
              Unifying.run
                ~env:
                  (Some { target = Wrap meta; undefined = (fun _ -> false); under_rigid = false })
              @@ fun () ->
              try Some (wrap (readback_neu rctx head vargs)) with Unsolvable _ -> None in
            contracted := !contracted @ [ attempt ]
        | None -> ());
        let k = CubeOf.dim xs in
        let ifilter = Modality.filter_idempotent filter in
        let free = CubeOf.build k { build = (fun _ -> true) } in
        let vbs = renamed_bindings rest ifilter (val_of_norm_cube xs) free in
        let dim = cod_left_ins ins in
        let vars, ty = renamed_binder ty filter dim xs in
        Renamed_args
          (Ctx.Ordered.invis rest ifilter vbs, (fun tm -> wrap (Lam (vars, dim, filter, tm))), ty)
    | Snoc (_, Field _) | Snoc (_, Inst _) -> raise_notrace Not_renaming in
  match (env, args) with
  (* If the environment is literally the identity environment of a context, and there are no arguments, that context itself is what we want. *)
  | Ctx mctx, Emp ->
      Some
        (Renamed_ctx
           {
             ctx = Ctx.of_ordered ~level mctx;
             check_type = false;
             in_image = (fun _ -> false);
             wrap = (fun tm -> tm);
             contracted = [];
           })
  | _ -> (
      match D.compare (dim_env env) D.zero with
      | Neq -> None
      | Eq -> (
          Reporter.discard_errors ~fallback:(fun () -> None) @@ fun () ->
          Displaying.run ~env:false @@ fun () ->
          Unifying.run
            ~env:(Some { target = Wrap meta; undefined = Hashtbl.mem counts; under_rigid = false })
          @@ fun () ->
          try
            scan mctx env;
            scan_args args;
            let (Renamed_ordered rest) = go mctx env in
            let ty =
              match args with
              | Emp -> None
              | _ -> Some (Norm.eval_term env mty) in
            let vspine = if !undefined then None else contractible v in
            let (Renamed_args (rest, wrap, _)) = go_args rest args ty vspine in
            Some
              (Renamed_ctx
                 {
                   ctx = Ctx.of_ordered ~level rest;
                   check_type = !undefined;
                   in_image = Hashtbl.mem counts;
                   wrap;
                   contracted = !contracted;
                 })
          with Not_renaming -> None))

(* Read back a value, at a type, as the solution of a unification metavariable in a renamed version of its context, or say why that's impossible: either rigidly, so that the value can't equal the metavariable however other metavariables are solved, or flexibly.  If anything is undefined in that context, the type can't contain it either; if it does, the failure is flexible, since other metavariables might be solved to remove it. *)
let readback_unif_solution : type mode a b x y.
    (mode, x, y, kinetic) Meta.t ->
    (mode, a, b) Ctx.t ->
    check_type:bool ->
    in_image:(level -> bool) ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    ((mode, b, kinetic) term, [ `Rigid | `Flexible ]) Result.t =
 fun meta ctx ~check_type ~in_image v ty ->
  Displaying.run ~env:false @@ fun () ->
  Unifying.run ~env:(Some { target = Wrap meta; undefined = in_image; under_rigid = false })
  @@ fun () ->
  match if check_type then ignore (readback_val ctx ty) with
  | exception Unsolvable _ -> Error `Flexible
  | () -> ( try Ok (readback_at Kinetic ctx v ty) with Unsolvable rigidity -> Error rigidity)
