(* This module should not be opened, but used qualified. *)

open Dim
open Reporter
open Value
open Modal
open Tctx

(* Remove the top entry from an environment.  Looks through lazy operations like Act, Shift, Unshift, and Permute, but no Keys are allowed to the right of the entry (which is ensured by the type). *)
let remove_top : type mode a modality k n.
    (mode, n, (a, (modality, k) dim_entry) suc) env -> (mode, n, a) env =
 fun env ->
  (* Because of the possibility of permutations, the recursion has to allow for the possibility of non-top elements, but still to the right of any keys. *)
  let rec remove_ins : type mode modality a k b n.
      (mode, n, b) env -> (a, modality, k, b) insert -> (mode, n, a) env =
   fun env v ->
    match (env, v) with
    | Emp _, _ -> .
    | Act (env, op), _ -> Act (remove_ins env v, op)
    | Key _, _ -> fatal (Anomaly "Key in remove_ins")
    | Permute (p, env), _ ->
        let (Permute_insert (v', p')) = permute_insert v p in
        Permute (p', remove_ins env v')
    | Ext (env, nk, modality, xs), Later v -> Ext (remove_ins env v, nk, modality, xs)
    | LazyExt (env, nk, modality, xs), Later v -> LazyExt (remove_ins env v, nk, modality, xs)
    | Ext (env, _, _, _), Now -> env
    | LazyExt (env, _, _, _), Now -> env
    | Shift (env, mn, nb), _ ->
        let (Uncoinsert (_, v', na)) = Plusmap.uncoinsert v nb in
        Shift (remove_ins env v', mn, na)
    | Unshift (env, mn, nb), _ ->
        let (Uninsert (_, v', na)) = Plusmap.uninsert v nb in
        Unshift (remove_ins env v', mn, na) in
  remove_ins env Now

(* Given an environment whose codomain context is extended by a partial context containing some locks, and starting with a lock if nonempty, split off as many keys as possible that could go with those locks, compose them up, and return them along with the remainder of the environment.  The type of this function doesn't determine what happens to keys in the environment with identity domain: they could stay on the environment or they could be accumulated into the returned cell.  We always accumulate them into the returned cell. *)

type (_, _, _, _, _) remove_keys =
  | Remove_keys :
      ('cod, 'n, 'b) env * ('mode, 'mu, 'nu, 'cod) Modalcell.t
      -> ('mode, 'mu, 'cod, 'n, 'b) remove_keys

(* TODO: This could also be a lazy constructor of environments, and we go through this process when we actually look up variables instead.  Then we wouldn't place other lazies like Permute, Shift, and Act back on the environment but rather act with them on the variable being looked up or the return result.  I don't know whether that would be likely to matter for performance. *)

let rec remove_keys : type mode mu cod k b bc.
    (mode, k, bc) env -> (b, cod, mu, mode, bc) plus_with_locks -> (mode, mu, cod, k, b) remove_keys
    =
 fun env (Plus_with_locks (swloe, bc, llc)) ->
  match (bc, llc, env) with
  (* If we encounter a key, we accumulate it.  Note that lmn and b_cmn could be Zero here: we continue accumulating keys until we run out of keys that we *could* include, not just until we run out of nonidentity locks in the codomain. *)
  | b_cn, llcn, Key (env, key, Plus_lock (ln, bc_n)) -> (
      let lln = locks_lock ln in
      let cn, n = (Locks.dom llcn, Lock.cod ln) in
      match Tctx.factor cn n with
      | None ->
          (* The type of this function doesn't rule this out: the decomposition of the length of the environment could land in the middle of the domain of a key.  We have to trust the caller to maintain the invariant. *)
          fatal (Anomaly "remove_keys: factor failure")
      | Some (Factor (_c, c_n)) ->
          let (Uncomp (llc, lln', m_n)) = Locks.uncomp c_n llcn in
          let Eq = Locks.uniq lln lln' in
          let b_c = Tctx.comp_assoc_cancelr c_n b_cn bc_n in
          let (Any swloe) = starts_with_lock_left c_n swloe in
          let (Remove_keys (e, keys)) = remove_keys env (Plus_with_locks (swloe, b_c, llc)) in
          let (Comp nus) = Modality.comp (Modalcell.vtgt key) in
          Remove_keys (e, Modalcell.hcomp m_n nus keys key))
  (* If we encounter a dimension entry, we skip it. *)
  | Suc (bc, Dim _), Suc (llc, Locks_dim _, Zero), _ ->
      let (Starts (Suc swloe)) = swloe in
      remove_keys (remove_top env) (Plus_with_locks (Starts swloe, bc, llc))
  (* If we encounter some other operation that could still have further keys inside it, we look through it. *)
  | _, _, Permute (p, env) ->
      (* This is where carrying around swloe is used, in decomposing the permutation. *)
      let (Unpermute (p, d, ad, lld)) = unpermute_plus_locks p swloe bc llc in
      let (Remove_keys (env, keys)) = remove_keys env (Plus_with_locks (d, ad, lld)) in
      Remove_keys (Permute (p, env), keys)
  | nb_nc, ll_nc, Shift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Dom_uncomp (nb, nc, b_c)) = Plusmap.dom_uncomp n nb_nc nbc in
      let (Eq _) = Plusmap.tgt nc in
      let swloe = Plusmap.dom_starts_with_lock_or_empty nc swloe in
      let ll_c = Plusmap.unlocks nc ll_nc in
      let (Remove_keys (env, keys)) = remove_keys env (Plus_with_locks (swloe, b_c, ll_c)) in
      Remove_keys (Shift (env, mn, nb), keys)
  | b_c, ll_c, Unshift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Uncomp (nb, nc, nb_nc)) = Plusmap.uncomp n b_c nbc in
      let (Eq _) = Plusmap.tgt nc in
      let swloe = Plusmap.cod_starts_with_lock_or_empty nc swloe in
      let ll_nc = Plusmap.locks n nc ll_c in
      let (Remove_keys (env, keys)) = remove_keys env (Plus_with_locks (swloe, nb_nc, ll_nc)) in
      Remove_keys (Unshift (env, mn, nb), keys)
  | _, _, Act (env, op) ->
      let (Remove_keys (env, keys)) = remove_keys env (Plus_with_locks (swloe, bc, llc)) in
      Remove_keys (Act (env, op), keys)
  (* If we reach the end of the environment, or a value entry, we bottom out the recursion, returning an identity key. *)
  | Zero, Zero _, Emp _ -> Remove_keys (env, Modalcell.id2 (mode_env env))
  | Zero, Zero _, LazyExt _ -> Remove_keys (env, Modalcell.id2 (mode_env env))
  | Zero, Zero _, Ext _ -> Remove_keys (env, Modalcell.id2 (mode_env env))
  (* Nothing else is possible, since if the tctx has a nonzero lock on it, the environment can't be empty or end with a value entry. *)
  | Suc (_, Lock _), Suc (_, Locks_lock _, Suc (_, _)), _ -> .
  | Suc (_, Proj _), Suc (_, _, _), _ -> .

(* As a special case, the context extension could consist only of locks. *)

let remove_keys_plus_lock : type mode mu cod k b bm.
    (mode, k, bm) env -> (b, cod, mu, mode, bm) plus_lock -> (mode, mu, cod, k, b) remove_keys =
 fun env plus -> remove_keys env (plus_with_locks_of_plus_lock plus)
