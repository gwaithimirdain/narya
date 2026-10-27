open Util
open Modal
open Tbwd
open Dim
open Value
open Tctx
open Reporter
open Ctx

(* For prekeys, all a smart constructor can do is ignore identities (on any modality). *)
let prekey_env : type mode mu nu cod n b.
    (mode, n, b) env -> (mode, mu, nu, cod) Modalcell.t -> (mode, n, b) env =
 fun env key -> if Modalcell.is_id key then env else Prekey (env, key)

(* Remove the top entry from an environment.  Looks through lazy operations like Act, Prekey, Shift, Unshift, and Permute.  No Locks are allowed to the right of the entry: this is ensured by the type, since an insert only passes dimension entries. *)
let remove_top : type mode a modality k n.
    (mode, n, (a, (modality, k) dim_entry) snoc) env -> (mode, n, a) env =
 fun env ->
  (* Because of the possibility of permutations, the recursion has to allow for the possibility of non-top elements. *)
  let rec remove_ins : type mode modality a k b n.
      (mode, n, b) env -> (a, modality, k, b) insert -> (mode, n, a) env =
   fun env v ->
    match (env, v) with
    | Emp _, _ -> .
    | Act (env, op), _ -> Act (remove_ins env v, op)
    | Lock _, _ -> .
    | Prekey (env, key), _ -> Prekey (remove_ins env v, key)
    | Permute (p, env), _ ->
        let (Permute_insert (v', p')) = permute_insert v p in
        Permute (p', remove_ins env v')
    | Ext e, Later v -> Ext { e with env = remove_ins e.env v }
    | Ext { env; _ }, Now -> env
    | Shift (env, mn, nb), _ ->
        let (Uncoinsert (_, _, v', na)) = Plusmap.uncoinsert v nb in
        Shift (remove_ins env v', mn, na)
    | Unshift (env, mn, nb), _ ->
        let (Uninsert (_, _, v', na)) = Plusmap.uninsert v nb in
        Unshift (remove_ins env v', mn, na)
    | Ctx ctx, _ -> remove_ins_ctx ctx v
  and remove_ins_ctx : type mode modality a k b c.
      (mode, c, b) Ordered_ctx.t -> (a, modality, k, b) insert -> (mode, D.zero, a) env =
   fun ctx v ->
    match (ctx, v) with
    | Snoc (ctx, _, _), Now -> Ctx ctx
    | Snoc (ctx, { filter; bindings; _ }, _), Later v ->
        env_ext (remove_ins_ctx ctx v) filter bindings
    | Weaken (ctx, _), _ -> remove_ins_ctx ctx v
    | Lock (_, _), _ | Emp _, _ -> . in
  remove_ins env Now

(* A prekey action is a key cell with a given mode as vertical source but existential vertical target (and horizontal target). *)
type _ prekey_action = Prekey_action : ('mode, 'm, 'n, 'cod) Modalcell.t -> 'mode prekey_action

(* Prewhisker a prekey action by a modality, transporting its vertical (and horizontal) source. *)
let prekey_prewhisker : type mode a b m n r.
    (mode, m, n, b) Modalcell.t -> (a, r, mode) Modality.t -> a prekey_action =
 fun pre mu ->
  let (Wrap pre) = Modalcell.prewhisker_wrapped pre mu in
  Prekey_action pre

(* Compose a prekey cell after an accumulated prekey action, both sharing the environment's mode as vertical source.  This is the general composition of key cells (as in act.ml's key_vcomp), using a pushout to reconcile the accumulated action's vertical target with the new prekey's vertical source. *)
let prekey_vcomp : type mode m n cod pm pn pcod.
    (mode, m, n, cod) Modalcell.t -> (mode, pm, pn, pcod) Modalcell.t -> mode prekey_action =
 fun key pre ->
  match Modality.pushout (Modalcell.vtgt pre) (Modalcell.vsrc key) with
  | Some (Pushout (mu3, mu4, cod13, dom24)) ->
      let (Comp cod24) = Modality.comp (Modalcell.vtgt key) in
      let (Comp dom13) = Modality.comp (Modalcell.vsrc pre) in
      Prekey_action
        (Modalcell.vcomp
           (Modalcell.hcomp dom24 cod24 (Modalcell.id mu4) key)
           (Modalcell.hcomp dom13 cod13 (Modalcell.id mu3) pre))
  | None -> fatal (Anomaly "prekey_vcomp: prekeys don't compose")

(* Given an environment whose codomain context is extended by a partial context containing some locks (and dimensions), strip off the Locks in the environment corresponding to those locks, and return the remainder of the environment along with a "prekey action" composed from all the Prekeys encountered along the way.  Since Locks carry no cells, any key action is represented by a Prekey; these act on a looked-up value at the environment's mode with a vertical target that may differ from the composite of the stripped locks, so they are accumulated separately and applied to the value at the end.  The prekeys accumulated inside a Lock act at its inner mode, so to carry them outward we prewhisker them by the lock's generator.  When no (nonidentity) prekeys are encountered, the returned cell is id2, and hence dropped by the smart constructor prekey_env.  Thus the input environment is semantically equal to the residual one, locked by the extension and then prekeyed by the returned cell. *)
type (_, _, _, _) restrict_keys =
  | Restrict_keys :
      ('cod, 'k, 'b) env * ('mode, 'pmu, 'pnu, 'pcod) Modalcell.t
      -> ('mode, 'cod, 'k, 'b) restrict_keys

let rec restrict_keys : type mode mu cod k b bc.
    (mode, k, bc) env -> (b, cod, mu, mode, bc) plus_with_locks -> (mode, cod, k, b) restrict_keys =
 fun env (Plus_with_locks (bc, llc)) ->
  match (bc, llc, env) with
  (* If we're out of locks to strip off, we bottom out the recursion, returning an identity prekey cell. *)
  | Zero, Zero _, _ -> Restrict_keys (env, Modalcell.id2 (mode_env env))
  (* If we encounter a Lock, it must match the outermost lock in the extension, which we consume. *)
  | Suc (bc, Lock g0), Suc (llc, Locks_lock g', Suc (Zero, _)), Lock (env, g) ->
      let Eq = Modality.Gen.src_uniq g0 g' in
      let Eq = Modality.Gen.tgt_uniq g0 g' in
      let Eq = Modality.Gen.src_uniq g g' in
      let Eq = Modality.Gen.tgt_uniq g g' in
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      let (Prekey_action pre) = prekey_prewhisker pre (Modality.of_gen g) in
      Restrict_keys (env, pre)
  (* If we encounter a dimension entry, we skip it. *)
  | Suc (bc, Dim _), Suc (llc, Locks_dim _, Zero), _ ->
      restrict_keys (remove_top env) (Plus_with_locks (bc, llc))
  (* A Proj is not possible due to the typing of contexts. *)
  | Suc (_, Proj _), Suc (_, _, _), _ -> .
  (* If we have more locks to strip off, but we find a prekey on the environment, that doesn't correspond to any locks in the codomain context, so we accumulate it into the prekey-action cell, which shares the environment's (unchanging) mode, composing it after any inner prekeys with the general key-cell composition.  Note that the extension could be exhausted here: we continue accumulating prekeys until we run out of ones that we *could* include. *)
  | (Suc _ as bc), llc, Prekey (env, key) ->
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      let (Prekey_action pre) = prekey_vcomp key pre in
      Restrict_keys (env, pre)
  (* If we encounter some other operation that could still have further locks inside it, we look through it. *)
  | Suc _, _, Permute (p, env) -> (
      match unpermute_plus_locks p bc llc with
      | Some (Unpermute (p, ad, lld)) ->
          let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (ad, lld)) in
          Restrict_keys (Permute (p, env), pre)
      | None ->
          (* This isn't ruled out: the permutation could mix the two parts of the decomposition.  We trust the caller to maintain the invariant. *)
          fatal (Anomaly "restrict_keys: unpermute failure"))
  | (Suc _ as nb_nc), ll_nc, Shift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Dom_uncomp (nb, nc, b_c)) = Plusmap.dom_uncomp n nb_nc nbc in
      let (Eq _) = Plusmap.tgt nc in
      let ll_c = Plusmap.unlocks nc ll_nc in
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (b_c, ll_c)) in
      Restrict_keys (Shift (env, mn, nb), pre)
  | (Suc _ as b_c), ll_c, Unshift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Uncomp (nb, nc, nb_nc)) = Plusmap.uncomp n b_c nbc in
      let (Eq _) = Plusmap.tgt nc in
      let ll_nc = Plusmap.locks n nc ll_c in
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (nb_nc, ll_nc)) in
      Restrict_keys (Unshift (env, mn, nb), pre)
  | Suc _, _, Act (env, op) ->
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      Restrict_keys (Act (env, op), pre)
  | Suc _, _, Ctx ctx -> restrict_keys (Ordered_ctx.unfold ctx) (Plus_with_locks (bc, llc))
