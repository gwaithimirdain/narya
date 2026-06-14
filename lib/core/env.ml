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
    | Ext e, Later v -> Ext { e with env = remove_ins e.env v }
    | Ext { env; _ }, Now -> env
    | Locked_ext e, Later v -> Locked_ext { e with env = remove_ins e.env v }
    | Locked_ext { env; _ }, Now -> env
    | Shift (env, mn, nb), _ ->
        let (Uncoinsert (_, _, v', na)) = Plusmap.uncoinsert v nb in
        Shift (remove_ins env v', mn, na)
    | Unshift (env, mn, nb), _ ->
        let (Uninsert (_, _, v', na)) = Plusmap.uninsert v nb in
        Unshift (remove_ins env v', mn, na) in
  remove_ins env Now

(* ******************** Filtering an environment's codomain ******************** *)

(* Filter an environment's codomain by a modality (the source of a nonparametric key under which it is being placed).  Each variable whose intrinsic dimension is already filtered for that modality is kept exactly as-is; each variable whose dimension is NOT already filtered "vanishes" -- its values are permanently inaccessible behind the key, so rather than try to filter its value cube (which would require choosing endpoints) we discard the data and leave a Locked_ext placeholder carrying the filtered dimension.  This relies on the fact that filtering commutes (Modality.filter_comm).  The new codomain is existential. *)

type (_, _) filtered_codomain =
  | Filtered_codomain : ('mode, 'm, 'b2) env -> ('mode, 'm) filtered_codomain

let rec filter_codomain : type mode m b dom sigma.
    (dom, sigma, mode) Modality.t -> (mode, m, b) env -> (mode, m) filtered_codomain =
 fun sigma env ->
  match env with
  | Emp (mode, m) -> Filtered_codomain (Emp (mode, m))
  | Ext { env = e; modality; filtered; filter; plus; values } -> (
      let (Filtered_codomain e') = filter_codomain sigma e in
      let k = D.plus_right plus in
      let (Has_filter f_sk) = Modality.filter sigma k in
      let k_s = Modality.filtered k f_sk in
      match D.compare k_s k with
      | Eq -> Filtered_codomain (Ext { env = e'; modality; filtered; filter; plus; values })
      | Neq ->
          (* The variable's dimension is not sigma-invariant, so it vanishes. *)
          let (Filter_comm (f_sk', fkk_s)) = Modality.filter_comm filtered f_sk in
          let Eq = Modality.filter_uniq f_sk' f_sk in
          Filtered_codomain (Locked_ext { env = e'; modality; dim = k_s; filtered = fkk_s }))
  | Locked_ext { env = e; modality; dim; filtered } ->
      let (Filtered_codomain e') = filter_codomain sigma e in
      Filtered_codomain (Locked_ext { env = e'; modality; dim; filtered })
  | Act (e, op) ->
      let (Filtered_codomain e') = filter_codomain sigma e in
      Filtered_codomain (Act (e', op))
  (* TODO: A permutation, nested key, shift, or unshift in the environment being filtered needs the codomain change transported across it; not yet implemented. *)
  | Permute _ -> fatal (Anomaly "filter_codomain: permutation not yet implemented")
  | Key _ -> fatal (Anomaly "filter_codomain: nested key not yet implemented")
  | Shift _ -> fatal (Anomaly "filter_codomain: nested shift not yet implemented")
  | Unshift _ -> fatal (Anomaly "filter_codomain: nested unshift not yet implemented")

(* ******************** Stripping keys ******************** *)

(* Given an environment whose codomain context is extended by a partial context containing some locks, split off as many keys as possible that could go with those locks, compose them up, and return them along with the bare environment lying underneath all of them.  Since the dimension of an environment is filtered as keys are added to it, the dimension of the bare environment can be larger than that of the input; we record the relation between the two by a filter (by the composite of the lock modalities, which is the vertical *source* of the composite of the keys) together with an operator collecting the intermediate operator actions, pushed outside the keys by filtering them.

   Note that intermediate shifts and unshifts can NOT be pushed outside the keys in this form, since they are not dimensional operators (they change the codomain context); so this function fails on them.  Use replace_keys, which rebuilds a complete environment, when they need to be handled. *)

type (_, _, _, _, _) stripped =
  | Stripped :
      ('cod, 'p, 'b) env
      * ('mode, 'nu, 'cod, 'q, 'p) Modality.filter_dim
      * ('k, 'q) op
      * ('mode, 'nu, 'nu2, 'cod) Modalcell.t
      -> ('mode, 'nu, 'cod, 'k, 'b) stripped

let rec strip_keys : type mode nu cod k b bc.
    (mode, k, bc) env -> (b, cod, nu, mode, bc) plus_with_locks -> (mode, nu, cod, k, b) stripped =
 fun env (Plus_with_locks (bc, llc)) ->
  match (bc, llc, env) with
  (* If we encounter a key, we accumulate it.  Note that the remaining locks could be Zero here: we continue accumulating keys until we run out of keys that we *could* include, not just until we run out of nonidentity locks in the codomain. *)
  | b_cn, llcn, Key (env1, filt1, key1, Plus_lock (ln, bc_n)) -> (
      let lln = locks_lock ln in
      let cn, n = (Locks.dom llcn, Lock.cod ln) in
      match Tctx.factor cn n with
      | None ->
          (* The type of this function doesn't rule this out: the decomposition of the length of the environment could land in the middle of the domain of a key.  We have to trust the caller to maintain the invariant. *)
          fatal (Anomaly "strip_keys: factor failure")
      | Some (Factor (_c, c_n)) ->
          let (Uncomp (llc, lln', m_n)) = Locks.uncomp c_n llcn in
          let Eq = Locks.uniq lln lln' in
          let b_c = Tctx.comp_assoc_cancelr c_n b_cn bc_n in
          let (Stripped (senv, f1, op1, keys)) = strip_keys env1 (Plus_with_locks (b_c, llc)) in
          (* Push the accumulated operator (which acts at the unfiltered dimension of the inner environment) outside this key by filtering it by the key's vertical source. *)
          let q1 = Modality.filtered (dim_env senv) f1 in
          let (Has_filter f_q1) = Modality.filter (Lock.dom ln) q1 in
          let (Filter_op (op1', f1')) = Modality.filter_op f_q1 op1 in
          let Eq = Modality.filter_uniq f1' filt1 in
          let (Comp nus) = Modality.comp (Modalcell.vtgt key1) in
          Stripped (senv, Modality.filter_comp m_n f1 f_q1, op1', Modalcell.hcomp m_n nus keys key1)
      )
  (* If we encounter a dimension entry while we have locks remaining to strip, we skip it. *)
  | Suc (bc, Dim _), Suc (llc, Locks_dim _, Zero), _ ->
      strip_keys (remove_top env) (Plus_with_locks (bc, llc))
  (* A permutation only permutes dimension entries, so we can transfer it to the bare environment, which has the same dimension entries in its prefix. *)
  | _, _, Permute (p, env1) -> (
      match unpermute_plus_locks p bc llc with
      | Some (Unpermute (p2, bd, lld)) ->
          let (Stripped (senv, f, op, keys)) = strip_keys env1 (Plus_with_locks (bd, lld)) in
          Stripped (Permute (p2, senv), f, op, keys)
      | None ->
          (* This isn't ruled out either: the permutation could mix the two parts of the decomposition.  Again, we trust the caller to maintain the invariant. *)
          fatal (Anomaly "strip_keys: unpermute failure"))
  (* An operator action accumulates into the returned operator. *)
  | _, _, Act (env1, op') ->
      let (Stripped (senv, f, op, keys)) = strip_keys env1 (Plus_with_locks (bc, llc)) in
      Stripped (senv, f, comp_op op op', keys)
  (* A shift or unshift interleaved with the keys cannot be expressed in the output of this function, since it modifies the codomain context of the bare environment as well as its dimension.  TODO: I don't see any reason why this couldn't happen, so we may eventually need to restructure. *)
  | _, _, Shift _ -> fatal (Anomaly "strip_keys: shift interleaved with keys unimplemented")
  | _, _, Unshift _ -> fatal (Anomaly "strip_keys: unshift interleaved with keys unimplemented")
  (* If we are out of locks to strip and we reach the end of the environment, or a value entry, we bottom out the recursion, returning an identity key. *)
  | Zero, Zero _, Emp _ ->
      Stripped
        ( env,
          Modality.filter_id (mode_env env) (dim_env env),
          id_op (dim_env env),
          Modalcell.id2 (mode_env env) )
  | Zero, Zero _, Ext _ ->
      Stripped
        ( env,
          Modality.filter_id (mode_env env) (dim_env env),
          id_op (dim_env env),
          Modalcell.id2 (mode_env env) )
  | Zero, Zero _, Locked_ext _ ->
      Stripped
        ( env,
          Modality.filter_id (mode_env env) (dim_env env),
          id_op (dim_env env),
          Modalcell.id2 (mode_env env) )
  (* Nothing else is possible, since if the tctx has a nonzero lock on it, the environment can't be empty or end with a value entry. *)
  | Suc (_, Lock _), Suc (_, Locks_lock _, Suc (_, _)), _ -> .
  | Suc (_, Proj _), Suc (_, _, _), _ -> .

(* ******************** Replacing keys ******************** *)

(* Given an environment whose codomain context is extended by a partial context containing some locks, replace all the keys that go with those locks by a single key: their horizontal composite, vertically composed with a given cell whose vertical target is the composite of those locks.  The locks on the new environment are those of the vertical source of the given cell, supplied as a plus_lock.

   Unlike strip_keys, this produces a complete new environment, so intermediate operator actions, shifts, and unshifts can be re-applied on the outside of the new key, pushed there by filtering them.  Since the given cell might have a more nonparametric source than the composite of the keys it replaces, the new key could filter the dimension more; we correct for this with degeneracies (filling the missing dimensions degenerately) so that the new environment has exactly the same dimension as the original.

   The recursion peels keys off from the outside in, accumulating their horizontal composite in 'acc'.  The vertical source 'sigma' of 'acc' is the composite of the locks consumed so far, and at each level the rebuilt environment has dimension equal to the sigma-filtering of the original dimension at that level; the returned filter witnesses this.  The argument 'sigma_comp' witnesses that the remaining locks composed with sigma equal the total nu, so that at the bottom acc is a cell with vertical source exactly nu, ready to be composed with the given cell. *)

type (_, _, _, _, _) replaced =
  | Replaced :
      ('amode, 'kk, 'brho) env * ('amode, 'sigma, 'mcur, 'kk, 'k) Modality.filter_dim
      -> ('amode, 'sigma, 'mcur, 'k, 'brho) replaced

(* At the bottom of the recursion, we attach the new key (the total accumulated keys vertically composed with the given cell) to the bare environment, and apply a degeneracy outside to bring the dimension back up from the mu-filtering to the nu-filtering. *)
let replace_bottom : type amode mu nu sigma tau cod k b brho.
    (cod, k, b) env ->
    (amode, nu, cod, cod id, cod, sigma) Modality.comp ->
    (amode, nu, tau, cod) Modalcell.t ->
    (amode, mu, sigma, cod) Modalcell.t ->
    (b, cod, mu, amode, brho) plus_lock ->
    (amode, nu, cod, k, brho) replaced =
 fun env sigma_comp acc cell plus_src ->
  let Eq = Modality.comp_uniq sigma_comp (Modality.id_comp (Modalcell.vsrc acc)) in
  let p = dim_env env in
  let (Has_filter f_mu) = Modality.filter (Modalcell.vsrc cell) p in
  let (Has_filter f_nu) = Modality.filter (Modalcell.vtgt cell) p in
  let keyed = key_env env f_mu (Modalcell.vcomp acc cell) plus_src in
  let d = Modalcell.filter_deg cell p f_mu f_nu in
  Replaced (act_env keyed (op_of_deg d), f_nu)

let rec replace_keys_rec : type amode mu nu tau cod sigma mcur murest k b bc brho.
    (mcur, k, bc) env ->
    (b, cod, murest, mcur, bc) plus_with_locks ->
    (amode, sigma, mcur, murest, cod, nu) Modality.comp ->
    (amode, sigma, tau, mcur) Modalcell.t ->
    (amode, mu, nu, cod) Modalcell.t ->
    (b, cod, mu, amode, brho) plus_lock ->
    (amode, sigma, mcur, k, brho) replaced =
 fun env (Plus_with_locks (bc, llc)) sigma_comp acc cell plus_src ->
  match (bc, llc, env) with
  (* If we encounter a key, we accumulate it horizontally onto acc, composing the consumed-locks witness appropriately. *)
  | b_cn, llcn, Key (env1, filt1, key1, Plus_lock (ln, bc_n)) -> (
      let lln = locks_lock ln in
      let cn, n = (Locks.dom llcn, Lock.cod ln) in
      match Tctx.factor cn n with
      | None -> fatal (Anomaly "replace_keys: factor failure")
      | Some (Factor (_c, c_n)) ->
          let (Uncomp (llc, lln', m_n)) = Locks.uncomp c_n llcn in
          let Eq = Locks.uniq lln lln' in
          let b_c = Tctx.comp_assoc_cancelr c_n b_cn bc_n in
          let sigma = Modalcell.vsrc acc in
          let (Comp s_mu1) = Modality.comp sigma in
          let sigma1_comp = Modality.comp_assocr m_n s_mu1 sigma_comp in
          let (Comp nus) = Modality.comp (Modalcell.vtgt acc) in
          let acc' = Modalcell.hcomp s_mu1 nus key1 acc in
          let (Replaced (env', f1)) =
            replace_keys_rec env1 (Plus_with_locks (b_c, llc)) sigma1_comp acc' cell plus_src in
          (* The key vanishes from the rebuilt environment; we just have to recompute the filter witness at this level, using the fact that filtering by (mu1 then sigma) is the same as filtering by mu1 and then by sigma. *)
          let (Has_filter f_sig) = Modality.filter sigma (dim_env env) in
          let f_comb = Modality.filter_comp s_mu1 filt1 f_sig in
          let Eq = Modality.filter_uniq f_comb f1 in
          Replaced (env', f_sig))
  (* If we encounter a dimension entry while we still have locks to strip off, we skip it. *)
  | Suc (bc, Dim _), Suc (llc, Locks_dim _, Zero), _ ->
      replace_keys_rec (remove_top env) (Plus_with_locks (bc, llc)) sigma_comp acc cell plus_src
  (* A permutation transfers to the rebuilt environment, extended by the identity on the new locks. *)
  | _, _, Permute (p, env1) -> (
      match unpermute_plus_locks p bc llc with
      | Some (Unpermute (p2, bd, lld)) ->
          let (Permute (q, pl_inner)) = permute_plus_lock (inv_perm p2) plus_src in
          let (Replaced (env', f)) =
            replace_keys_rec env1 (Plus_with_locks (bd, lld)) sigma_comp acc cell pl_inner in
          Replaced (Permute (inv_perm q, env'), f)
      | None -> fatal (Anomaly "replace_keys: unpermute failure"))
  (* An operator action gets pushed outside the new key by filtering it by sigma, using the filter witness returned by the recursive call. *)
  | _, _, Act (env1, op) ->
      let (Replaced (env', f1)) =
        replace_keys_rec env1 (Plus_with_locks (bc, llc)) sigma_comp acc cell plus_src in
      let (Filter_op (op', f')) = Modality.filter_op f1 op in
      Replaced (act_env env' op', f')
  (* A shift also gets pushed outside the new key.  The rebuilt inner environment has dimension sigma(m+n) = sigma(m)+sigma(n), but the rebuilt shift must add the full dimension n to the (new) codomain context; so we first apply a degeneracy filling the missing directions of n degenerately. *)
  | b_cn, ll_cn, Shift (env1, n_x, xb) ->
      let x = D.plus_right n_x in
      let (Dom_uncomp (nbm, ncm, b_c)) = Plusmap.dom_uncomp x b_cn xb in
      let (Eq _) = Plusmap.tgt ncm in
      let ll_c = Plusmap.unlocks ncm ll_cn in
      let (Unshift (pm', pl_inner)) = unshift_unplus_lock x nbm plus_src in
      let (Replaced (env', f1)) =
        replace_keys_rec env1 (Plus_with_locks (b_c, ll_c)) sigma_comp acc cell pl_inner in
      let (Filter_of_plus (sn_sx, f_nd, f_x)) = Modality.filter_of_plus n_x f1 in
      let dx = Modality.deg_of_filter x f_x in
      let snd = Modality.filtered (D.plus_left n_x (dim_env env1)) f_nd in
      let (Plus snd_x) = D.plus x in
      let env'' = act_env env' (op_of_deg (plus_deg snd sn_sx snd_x dx)) in
      Replaced (Value.Shift (env'', snd_x, pm'), f_nd)
  (* An unshift likewise gets pushed outside the new key.  Here the rebuilt unshift adds the full dimension n while the output should contain only sigma(n); we restrict to the included face, fixing an endpoint in the missing directions of n (which is semantically harmless since the data there is inaccessible behind the nonparametric locks). *)
  | b_c, ll_c, Unshift (env1, n_x, xb) ->
      let x = D.plus_right n_x in
      let (Uncomp (nbm, ncm, nb_nc)) = Plusmap.uncomp x b_c xb in
      let (Eq _) = Plusmap.tgt ncm in
      let ll_nc = Plusmap.locks x ncm ll_c in
      let (Shift (pm', pl_inner)) = shift_unplus_lock x nbm plus_src in
      let (Replaced (env', f1)) =
        replace_keys_rec env1 (Plus_with_locks (nb_nc, ll_nc)) sigma_comp acc cell pl_inner in
      let (Plus kk1_x) = D.plus x in
      let unshifted = Value.Unshift (env', kk1_x, pm') in
      let (Has_filter f_x) = Modality.filter (Modalcell.vsrc acc) x in
      let fc = Modality.sface_of_filter x f_x in
      let kk1 = Modality.filtered (dim_env env1) f1 in
      let (Plus kk1_sx) = D.plus (Modality.filtered x f_x) in
      let env'' = act_env unshifted (op_of_sface (plus_sface kk1 kk1_x kk1_sx fc)) in
      Replaced (env'', Modality.filter_plus kk1_sx n_x f1 f_x)
  (* If we reach the end of the environment, or a value entry, we bottom out the recursion.  Here the locks are all consumed, so sigma is the total nu, as witnessed by sigma_comp. *)
  | Zero, Zero _, Emp _ -> replace_bottom env sigma_comp acc cell plus_src
  | Zero, Zero _, Ext _ -> replace_bottom env sigma_comp acc cell plus_src
  | Zero, Zero _, Locked_ext _ -> replace_bottom env sigma_comp acc cell plus_src
  (* Nothing else is possible, since if the tctx has a nonzero lock on it, the environment can't be empty or end with a value entry. *)
  | Suc (_, Lock _), Suc (_, Locks_lock _, Suc (_, _)), _ -> .
  | Suc (_, Proj _), Suc (_, _, _), _ -> .

let replace_keys : type amode mu nu cod k a ac am.
    (amode, k, ac) env ->
    (a, cod, nu, amode, ac) plus_with_locks ->
    (amode, mu, nu, cod) Modalcell.t ->
    (a, cod, mu, amode, am) plus_lock ->
    (amode, k, am) env =
 fun env plus_tgt cell plus_src ->
  let amode = mode_env env in
  let (Replaced (env', f)) =
    replace_keys_rec env plus_tgt
      (Modality.comp_id (Modalcell.vtgt cell))
      (Modalcell.id2 amode) cell plus_src in
  let Eq = Modality.eq_of_filter_id f in
  env'
