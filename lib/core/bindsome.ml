open Util
open Modal
open Tbwd
open Tlist
open Dim
open Tctx
open Reporter
open Value
open Norm
open Readback
module Binding = Ctx.Binding

(* We will need to be able to "flatten" lists of nats into single nats, in a way that works on forwards lists (of backwards nats!) as well as backwards ones, and also respects permutations.  We obtain this as the monoid homomorphism from the free monoid on N to N itself induced by the identity function of N. *)

(* We add forwardness from Fwn to the module N to make a MonoidPermFwd. *)
module NFwd = struct
  include N

  type 'n fwd = 'n Fwn.t
  type fwd_zero = Fwn.zero

  let fwd_zero = Fwn.zero

  type ('a, 'n, 'an) bplus = ('a, 'n, 'an) Fwn.bplus

  let bplus_zero = Fwn.bplus_zero

  (* Apparently we can't actually use the type Fwn.has_bplus, since the signature of MonoidFwd requires it to be a *new* type defined there. *)
  type (_, _) has_bplus = Bplus : ('a, 'b, 'ab) bplus -> ('a, 'b) has_bplus

  let bplus : type a b. b fwd -> (a, b) has_bplus =
   fun b ->
    let (Bplus ab) = Fwn.bplus b in
    Bplus ab

  type ('a, 'n, 'an) fplus = ('a, 'n, 'an) Fwn.fplus

  let bfplus_assocr = Fwn.bfplus_assocr
end

module IdN = struct
  module Dom = N
  module Cod = NFwd

  type (_, _) t = Id : 'x N.t -> ('x, 'x) t

  let dom : type a x. (a, x) t -> a Dom.t = fun (Id x) -> x
  let cod : type a x. (a, x) t -> x Cod.t = fun (Id x) -> x

  type _ exists = Exists : ('a, 'x) t -> 'a exists

  let exists : type a. a Dom.t -> a exists = fun x -> Exists (Id x)

  let uniq : type a x1 x2. (a, x1) t -> (a, x2) t -> (x1, x2) Eq.t =
   fun ix iy ->
    match (ix, iy) with
    | Id _, Id _ -> Eq
end

(* Here is the monoid homomorphism. *)
module Flatten = Word.HomPermFwd (N) (NFwd) (IdN)
module Nbwd = Flatten.Dom

(* The caller of bind_some passes it a hashtable associating level variables to the normals to which they are to be re-bound.  Normals are parametrized by mode, and all the variables to be re-bound are always at the same mode.  But they might start out behind some locks in the context, so we need to check when doing the rebinding that the modes agree; hence we store the mode along with the hashtable. *)

type 'mode var_binder = 'mode Mode.t * (level, 'mode normal) Hashtbl.t

let bind_var : type bindmode mode. bindmode var_binder -> level -> mode Mode.t -> mode normal option
    =
 fun (bindmode, vars) lvl mode ->
  match Mode.compare bindmode mode with
  | Eq -> Hashtbl.find_opt vars lvl
  | Neq -> None

module Ordered = struct
  open Ctx.Ordered

  (* Ordinary contexts are "backwards" lists.  Following Cockx's thesis, in this file we call the forwards version "telescopes", since they generally are going to get appended to a "real", backwards, context.  A telescope has *five* indices:

     -1. The mode at its left-hand point, i.e. the mode of a context it could get appended to.
     0. The mode at its right-hand point, i.e. the mode of the result context after appending.
     1. A raw length that is a forwards natural number, like the backwards natural numbers that are the raw indices of contexts.
     3. A checked length that is a forwards list of dimensions and locks, like the backwards list of dimensions and locks that are the checked indices of contexts.  To make the modes match up, this is actually a Tctx.fwd.
     2. A forwards Tlist of backwards natural numbers that flattens to the raw length.  We could index contexts by an analogous backwards Tbwd of nats, but we don't have any need for that so far.  But retaining this index for telescopes is crucial to constructing the correct permutations in bind_some, below, in an intrinsically well-typed way. *)
  type ('lmode, 'rmode, _, _, _) tel =
    | Nil : 'mode Mode.t -> ('mode, 'mode, Fwn.zero, nil, 'mode id) tel
    | Cons :
        ('ldom, 'lmodality, 'lmode, 'x, 'n) Ctx.entry
        * ('lmode, 'rmode, 'a, 'f, 'b) tel
        * ('x, 'a, 'xa) Fwn.fplus
        -> ('lmode, 'rmode, 'xa, ('x, 'f) cons, (('lmodality, 'n) dim_entry, 'b) cons) tel
    | Lock :
        ('lmode, 'modality, 'cod) Modality.gen * ('lmode, 'rmode, 'i, 'f, 'a) tel
        -> ('cod, 'rmode, 'i, 'f, ('modality lock_entry, 'a) cons) tel
    | Parametric_lock : ('lmode, 'rmode, 'x, 'f, 'b) tel -> ('lmode, 'rmode, 'x, 'f, 'b) tel
    (* A weakening entry contributes one raw variable (its nat block is N.one) but no checked entry.  Dual to Lock, which contributes a checked entry but no raw variable. *)
    | Weaken :
        ('lmode, 'rmode, 'a, 'f, 'b) tel * Reporter.Code.t * (N.one, 'a, 'xa) Fwn.fplus
        -> ('lmode, 'rmode, 'xa, (N.one, 'f) cons, 'b) tel

  (* The second index does in fact flatten to the first. *)
  let rec tel_flatten : type lmode rmode i f a. (lmode, rmode, i, f, a) tel -> (f, i) Flatten.fwd =
    function
    | Nil _ -> Zero
    | Cons (e, tel, xa) -> Suc (Id (Ctx.raw_entry e), tel_flatten tel, xa)
    | Lock (_, tel) -> tel_flatten tel
    | Parametric_lock tel -> tel_flatten tel
    | Weaken (tel, _, xa) -> Suc (Id (Fwn.fplus_left xa), tel_flatten tel, xa)

  let rec mode_tel : type lmode rmode i f a. (lmode, rmode, i, f, a) tel -> lmode Mode.t = function
    | Nil mode -> mode
    | Cons (_, tel, _) -> mode_tel tel
    | Lock (modality, _) -> Modality.Gen.tgt modality
    | Parametric_lock tel -> mode_tel tel
    | Weaken (tel, _, _) -> mode_tel tel

  (* Convert a context to a telescope. *)
  type ('rmode, 'i, 'b) to_tel =
    | To_tel :
        (N.zero, 'j, 'i) Fwn.bplus
        * ('rmode, 'c, 'lmode, 'lmode emp, unit, 'b) Tctx.bcomp
        * ('lmode, 'rmode, 'j, 'ff, 'c) tel
        -> ('rmode, 'i, 'b) to_tel

  let to_tel : type mode i b. (mode, i, b) Ctx.Ordered.t -> (mode, i, b) to_tel =
   fun ctx ->
    let rec go : type lmode rmode j ff c i ij b bc.
        (lmode, i, b) Ctx.Ordered.t ->
        (lmode, rmode, j, ff, c) tel ->
        (i, j, ij) Fwn.bplus ->
        (rmode, c, lmode, b, unit, bc) Tctx.bcomp ->
        (rmode, ij, bc) to_tel =
     fun ctx tel ij bc ->
      match ctx with
      | Emp _ -> To_tel (ij, bc, tel)
      | Snoc (ctx, e, ax) ->
          let (Fplus xf) = Fwn.fplus (N.plus_right ax) in
          go ctx
            (Cons (e, tel, xf))
            (Fwn.bfplus_assocr ax xf ij)
            (Suc (Dim (Ctx.dim_entry e, Ctx.filter_entry e), bc))
      | Lock (ctx, modality) -> go ctx (Lock (modality, tel)) ij (Suc (Lock modality, bc))
      | Weaken (ctx, code) ->
          let (Fplus xf) = Fwn.fplus N.one in
          go ctx (Weaken (tel, code, xf)) (Fwn.bfplus_assocr (Suc Zero) xf ij) bc in
    go ctx (Nil (mode ctx)) Zero Zero

  (* Now we begin the suite of helper functions for bind_some.  This is an operation that happens during typechecking a pattern match, when the match variable along with all its indices have to be replaced by values determined by the constructor of each branch.  This requires the context to be re-sorted at the same time to maintain a consistent dependency structure, with each type and value depending only on the variables to its left.  It also requires "substitution into values", which we do by reading back values into the old context and then evaluating them in the new context.  This readback also has the double purpose of checking which types make sense in a given context, to determine a correct permutation.

     Here are functions that perform this eval-readback cycle on normal forms and values.  The 'oldctx' here is nonstandard in that its level variables may appear out of order, because it's been created by partially permuting the variables in an existing context.  Therefore, in order to ensure that new level variables created in that context (during readback) don't conflict with any existing ones, we have to be passed the maximum level of the *original* context it was built from. *)

  let eval_readback_nf : type mode a b.
      level:int ->
      oldctx:(mode, a, b) Ctx.Ordered.t ->
      newctx:(mode, a, b) Ctx.Ordered.t ->
      mode normal ->
      mode normal option =
   fun ~level ~oldctx ~newctx nf ->
    Reporter.try_with ~fatal:(fun d ->
        match d.message with
        | No_such_level _ -> None
        | _ -> fatal_diagnostic d)
    @@ fun () ->
    Some
      {
        tm = eval_term (Ctx.Ordered.env newctx) (readback_nf (Ctx.of_ordered ~level oldctx) nf);
        ty = eval_term (Ctx.Ordered.env newctx) (readback_val (Ctx.of_ordered ~level oldctx) nf.ty);
      }

  let eval_readback_val : type mode a b.
      level:int ->
      oldctx:(mode, a, b) Ctx.Ordered.t ->
      newctx:(mode, a, b) Ctx.Ordered.t ->
      (mode, kinetic) value ->
      (mode, kinetic) value option =
   fun ~level ~oldctx ~newctx ty ->
    Reporter.try_with ~fatal:(fun d ->
        match d.message with
        | No_such_level _ -> None
        | _ -> fatal_diagnostic d)
    @@ fun () ->
    Some (eval_term (Ctx.Ordered.env newctx) (readback_val (Ctx.of_ordered ~level oldctx) ty))

  (* We define bind_some and its helper functions in reverse order from the order in which they're called, so that each one can call the already-defined next one in line.  We could put them in the other order by making them mutual, but I prefer to avoid mutuality when it's unnecessary, and also this way each one can be next to the definition of its GADT return type.  But it is probably better to read them in reverse order, starting with bind_some lower down.  The call process goes as follows:

     1. Typechecking during a match calls bind_some, passing it the context and a table (var_binder, defined above) that picks out the level variables to be re-bound and their associated values (which are in that context).

     2. bind_some calls to_tel to shuffle the context entirely to the right into a telescope and compute the corresponding Tlist of nats and flattened forwards nat (representing the same raw length).  Then it calls go_bind_some with these data and two empty contexts "oldctx" and "newctx".

     3. go_bind_some is passed (in addition to the rebinding table and flattening data) two contexts of the same (raw and checked) lengths, oldctx and newctx, as well as a telescope.  It and its callees maintain the invariant that oldctx appended by the telescope is a permutation of the old context, containing the *old* level variables and their types, unsubstituted by the rebinding callback (now no longer in order); while newctx contains the same entries as oldctx, in the same order (which is the new correct order), but now with new level variables and the rebinding substitutions made.  The function go_bind_some repeatedly calls go_go_bind_some, finally returning a completed permuted context, along with data recording the resulting permutation and flattening.

     4. go_go_bind_some is passed mostly the same data as go_bind_some, but its job is only to find the *next* variable from the unprocessed telescope to add to oldctx and newctx.  Thus, it recurses through that telescope, trying for each cube of variables to readback all the types and values in oldctx and then evaluate them in newctx.  As soon as it finds one that succeeds, it excises that entry from the telescope and returns both the old entry, the readback-evaluated version, and the telescope with that entry removed (plus information about where it was removed from, which is used to construct the permutations).  It also fails if it encounters a nontrivial context lock after skipping some entries, since permutation should only occur in a string of variables between locks.

     5. Thus, go_bind_some proceeds by calling go_go_bind_some, adding the returned entries to oldctx and newctx, and then calling itself recursively on the remaining telescope.  If the telescope is emptied, we have succeeded and we return.  But if go_go_bind_some fails on all entries of a nonempty telescope, the whole process fails.  (I think this should never happen and indicates a bug; anything the user might do that would cause that should be caught earlier.)

     6. go_go_bind_some acts on each entry with bind_some_entry, whose real work is done by bind_some_normal_cube that acts on a cube of variables with the binder callback and readback-eval.  Since that function is the one we define first, we now proceed to comment its definition directly. *)

  let bind_some_normal_cube : type dom modality mode bindmode i a k n.
      level:int ->
      bindmode var_binder ->
      [ `Bindable | `Nonbindable ] ->
      oldctx:(mode, i, a) Ctx.Ordered.t ->
      newctx:(mode, i, a) Ctx.Ordered.t ->
      (dom, modality, mode, k, n) Modality.filter_dim ->
      (k, dom Binding.t) CubeOf.t ->
      (k, dom Binding.t) CubeOf.t option =
   fun ~level binder bindable ~oldctx ~newctx filter in_entry ->
    let i = Ctx.Ordered.length newctx in
    let modality = Modality.filter_modality filter in
    let filtered = Modality.filter_idempotent filter in
    (* The tricky thing we have to deal with is that in a *cube* of variables, when doing readback-eval on each variable, we should be allowed to use the *preceeding* variables in the dependency order of the cube, but not the *subsequent* ones.  Unfortunately we don't have a direct way for a context to contain only "some" of a cube of variables.  Thus, we use the ability of Binder.t to be Unknown or Delayed.  *)
    (* We start by creating two variable cubes from the given one.  In "oldentry" all the variables have the same values, but they are delayed so that we can't use them until we've gotten past them in iterating through the cube.  In "newentry" the variables all have unknown values, which we will specify later after eval-readback succeeds step by step. *)
    let [ oldentry; newentry ] =
      CubeOf.pmap
        { map = (fun _ [ b ] -> [ Binding.delay b; Binding.unknown () ]) }
        [ in_entry ] (Cons (Cons Nil)) in
    (* Now we temporarily add both of those entries to the given contexts.  Since we are not using these contexts for typechecking, they might as well be invisible. *)
    let (Locked (plus, oldctx)) =
      Ctx.Ordered.lock (Ctx.Ordered.invis oldctx filtered oldentry) modality in
    let newctx = Ctx.Ordered.lock_to (Ctx.Ordered.invis newctx filtered newentry) modality plus in
    (* The integer k counts the second component of the new level variables we are creating. *)
    let k = ref 0 in
    (* We short-circuit out of the cube iteration with an exception if any variable's readback-eval fails (returns None). *)
    let exception Short_circuit in
    try
      CubeOf.miter
        {
          it =
            (fun fa [ b; oldb; newb ] ->
              let new_level = (i, !k) in
              k := !k + 1;
              match Binding.level b with
              | None -> (
                  (* If the variable was let-bound in the original context, we readback-eval its (normal) value, which includes its type. *)
                  let oldnf = Binding.value b in
                  match eval_readback_nf ~level ~oldctx ~newctx oldnf with
                  | Some newnf ->
                      (* Now we allow this variable to be used when reading back other variables, and specify the newly evaluated version to be used in the new context. *)
                      Binding.force oldb;
                      Binding.specify newb None newnf
                  | None -> raise_notrace Short_circuit)
              | Some old_level -> (
                  (* For variables that were not let-bound in the old context, we first check whether we're newly binding them. *)
                  match bind_var binder old_level (Modality.src modality) with
                  (* `Nonbindable means only that the *top* variable is nonbindable. *)
                  | Some oldnf when bindable = `Bindable || Option.is_none (is_id_sface fa) -> (
                      (* If so, then the value returned by the binder callback is in the old context, so we readback-eval it and proceed as before. *)
                      match eval_readback_nf ~level ~oldctx ~newctx oldnf with
                      | Some newnf ->
                          Binding.force oldb;
                          Binding.specify newb None newnf
                      | None -> raise_notrace Short_circuit)
                  | None -> (
                      (* Otherwise, we readback-eval only its type, and create a new De Bruijn level for the new context. *)
                      let oldnf = Binding.value b in
                      let oldty = oldnf.ty in
                      match eval_readback_val ~level ~oldctx ~newctx oldty with
                      | Some newty ->
                          let newnf = { tm = var modality new_level newty; ty = newty } in
                          Binding.force oldb;
                          Binding.specify newb (Some new_level) newnf
                      | None -> raise_notrace Short_circuit)
                  | _ -> fatal (Anomaly "attempt to bind variable with field views")));
        }
        [ in_entry; oldentry; newentry ];
      Some newentry
    with Short_circuit -> None

  let bind_some_entry : type dom modality mode bindmode f i a n.
      level:int ->
      bindmode var_binder ->
      oldctx:(mode, i, a) Ctx.Ordered.t ->
      newctx:(mode, i, a) Ctx.Ordered.t ->
      (dom, modality, mode, f, n) Ctx.entry ->
      (dom, modality, mode, f, n) Ctx.entry option =
   fun ~level binder ~oldctx ~newctx e ->
    let open Monad.Ops (Monad.Maybe) in
    match e with
    | Vis ({ filter; bindings; fplus = Zero; _ } as v) ->
        let* bindings =
          bind_some_normal_cube ~level binder `Bindable ~oldctx ~newctx filter bindings in
        return (Ctx.Vis { v with bindings })
    | Invis { filter; bindings } ->
        let* bindings =
          bind_some_normal_cube ~level binder `Bindable ~oldctx ~newctx filter bindings in
        return (Ctx.Invis { filter; bindings })
    | Vis ({ filter; bindings; _ } as v) ->
        (* A variable that has views of its fields can't be bound. *)
        let* bindings =
          bind_some_normal_cube ~level binder `Nonbindable ~oldctx ~newctx filter bindings in
        return (Ctx.Vis { v with bindings })

  (* This seems an appropriate place to comment about the "insert" and "append_permute" data being returned from (go_)go_bind_some.  The issue is that in addition to a permuted context, we need to compute the permutation relating it to the original context.  In fact we need *two* permutations, one for the raw indices and one for the checked indices.

     The one for the checked indices is more straightforward to compute, because the checked indices are a list of dimensions and we construct the permutation directly working with that list.  Our definition of permutations in terms of iterated insertions closely matches how we construct the permutation, picking out one entry at a time from the remaining ones.  The data structure Tbwd.append_permute is designed to capture the construction of a permutation in this way.

     The one for the raw indices is trickier because it acts as a "block" permutation, with all the raw variables in each Split entry being permuted as a group.  It seems that this permutation should be determined by the permutation of checked indices, but confusingly, that isn't quite true, because the number of raw indices corresponding to a single cube of variables (which is one entry in the checked-index dimension list) depends on what kind of entry it is -- visible, invisible, or split -- which is not recorded in the index *type*.  Our solution is to construct, as we go along, a parallel type list of *natural numbers*, which flattens to the raw index type, and a permutation of it.  Thus go_go_bind some returns *two* 'Tlist.insert's, and go_bind_some returns *two* 'Tbwd.append_permute's, while bind_some flattens and dices them to make a single N.perm and Tbwd.permute. *)

  type (_, _, _, _, _) go_go_bind_some =
    | Found : {
        oldentry : ('ldom, 'lmodality, 'lmode, 'f, 'n) Ctx.entry;
        newentry : ('ldom, 'lmodality, 'lmode, 'f, 'n) Ctx.entry;
        ins : ('b, 'lmodality, 'n, 'c, 'lmode) fwd_insert;
        fins : ('bf, 'f, 'cf) Tlist.insert;
        rest : ('lmode, 'rmode, 'i, 'bf, 'b) tel;
      }
        -> ('lmode, 'rmode, 'j, 'c, 'cf) go_go_bind_some
    | Lock :
        ('ldom, 'lmodality, 'lmode) Modality.gen * ('ldom, 'rmode, 'i, 'cf, 'c) tel
        -> ('lmode, 'rmode, 'i, ('lmodality lock_entry, 'c) cons, 'cf) go_go_bind_some
    | Parametric_lock :
        ('ldom, 'rmode, 'i, 'cf, 'c) tel
        -> ('ldom, 'rmode, 'i, 'c, 'cf) go_go_bind_some
    | Weaken :
        ('lmode, 'rmode, 'a, 'f, 'c) tel * Reporter.Code.t * (N.one, 'a, 'xa) Fwn.fplus
        -> ('lmode, 'rmode, 'xa, 'c, (N.one, 'f) cons) go_go_bind_some
    | Nil : ('mode, 'mode, Fwn.zero, 'mode id, nil) go_go_bind_some
    | None : ('lmode, 'rmode, 'i, 'c, 'cf) go_go_bind_some

  let rec go_go_bind_some : type lmode rmode bindmode i j a c cf.
      level:int ->
      bindmode var_binder ->
      oldctx:(lmode, i, a) Ctx.Ordered.t ->
      newctx:(lmode, i, a) Ctx.Ordered.t ->
      (lmode, rmode, j, cf, c) tel ->
      (lmode, rmode, j, c, cf) go_go_bind_some =
   fun ~level binder ~oldctx ~newctx tel ->
    match tel with
    | Nil _ -> Nil
    | Cons (entry, rest, _) -> (
        match bind_some_entry ~level binder ~oldctx ~newctx entry with
        | Some newentry ->
            Found
              {
                ins = Now (Ctx.dim_entry newentry, Ctx.filter_entry newentry);
                fins = Now;
                oldentry = entry;
                newentry;
                rest;
              }
        | None -> (
            match go_go_bind_some ~level binder ~oldctx ~newctx rest with
            | Found { ins; oldentry; newentry; rest; fins } ->
                let (Fplus newfaces) = Fwn.fplus (Ctx.raw_entry entry) in
                Found
                  {
                    ins = Later (Ctx.modality_entry entry, ins);
                    oldentry;
                    newentry;
                    rest = Cons (entry, rest, newfaces);
                    fins = Later fins;
                  }
            | Nil | None | Lock _ | Parametric_lock _ | Weaken _ -> None))
    | Lock (lock, tel) -> Lock (lock, tel)
    | Parametric_lock tel -> Parametric_lock tel
    | Weaken (tel, code, xf) -> Weaken (tel, code, xf)

  type ('rmode, 'lmode, 'i, 'j, 'a, 'af, 'b, 'bf) go_bind_some =
    | Go_bind_some : {
        raw_flat : ('cf, 'k) Flatten.t;
        raw_perm : ('af, 'bf, 'cf) Tbwd.append_permute;
        checked_perm : ('rmode, 'b, 'lmode, 'a, unit, 'c) bcomp_permute;
        newctx : ('rmode, 'k, 'c) Ctx.Ordered.t;
        oldctx : ('rmode, 'k, 'c) Ctx.Ordered.t;
      }
        -> ('rmode, 'lmode, 'i, 'j, 'a, 'af, 'b, 'bf) go_bind_some
    | None : ('rmode, 'lmode, 'i, 'j, 'a, 'af, 'b, 'bf) go_bind_some

  let rec go_bind_some : type lmode rmode bindmode i j a af b bf.
      level:int ->
      bindmode var_binder ->
      oldctx:(lmode, i, a) Ctx.Ordered.t ->
      newctx:(lmode, i, a) Ctx.Ordered.t ->
      (af, i) Flatten.t ->
      (lmode, rmode, j, bf, b) tel ->
      (rmode, lmode, i, j, a, af, b, bf) go_bind_some =
   fun ~level binder ~oldctx ~newctx af tel ->
    match go_go_bind_some ~level binder ~oldctx ~newctx tel with
    | Found { ins; fins; oldentry; newentry; rest } -> (
        let k = Ctx.raw_entry oldentry in
        let (Plus faces) = N.plus k in
        let oldctx = Snoc (oldctx, oldentry, faces) in
        let newctx = Snoc (newctx, newentry, faces) in
        match go_bind_some ~level binder ~oldctx ~newctx (Suc (af, Id k, faces)) rest with
        | Go_bind_some { raw_flat; raw_perm; checked_perm; oldctx; newctx } ->
            Go_bind_some
              {
                raw_flat;
                raw_perm = Ap_insert (fins, raw_perm);
                checked_perm = Insert (ins, checked_perm);
                oldctx;
                newctx;
              }
        | None -> None)
    | Nil ->
        Go_bind_some { raw_flat = af; raw_perm = Ap_nil; checked_perm = Id Zero; oldctx; newctx }
    | None -> None
    | Lock (modality, rest) -> (
        let oldctx = Ctx.Ordered.Lock (oldctx, modality) in
        let newctx = Ctx.Ordered.Lock (newctx, modality) in
        match go_bind_some ~level binder ~oldctx ~newctx af rest with
        | Go_bind_some g -> Go_bind_some { g with checked_perm = Lock (modality, g.checked_perm) }
        | None -> None)
    | Parametric_lock tel -> go_bind_some ~level binder ~oldctx ~newctx af tel
    | Weaken (rest, code, xf) -> (
        (* A weakening entry adds a raw variable but no checked entry, so we insert its one-variable block into the raw permutation and leave the checked permutation unchanged.  Like a lock, it acts as a barrier: variables are not permuted across it. *)
        let oldctx = Ctx.Ordered.Weaken (oldctx, code) in
        let newctx = Ctx.Ordered.Weaken (newctx, code) in
        match
          go_bind_some ~level binder ~oldctx ~newctx
            (Suc (af, Id (Fwn.fplus_left xf), Suc Zero))
            rest
        with
        | Go_bind_some g -> Go_bind_some { g with raw_perm = Ap_insert (Now, g.raw_perm) }
        | None -> None)

  type (_, _, _) bind_some =
    | Bind_some : {
        raw_perm : ('a, 'i) N.permute;
        checked_perm : ('c, 'b) permute;
        oldctx : ('mode, 'i, 'c) Ctx.Ordered.t;
        newctx : ('mode, 'i, 'c) Ctx.Ordered.t;
      }
        -> ('mode, 'a, 'b) bind_some
    | None : ('mode, 'a, 'b) bind_some

  let bind_some : type mode bindmode a b.
      level:int -> bindmode var_binder -> (mode, a, b) Ctx.Ordered.t -> (mode, a, b) bind_some =
   fun ~level binder ctx ->
    let (To_tel (bplus_raw, checked_append, tel)) = to_tel ctx in
    let telf = tel_flatten tel in
    match
      go_bind_some ~level binder
        ~oldctx:(empty (mode_tel tel))
        ~newctx:(empty (mode_tel tel))
        Zero tel
    with
    | Go_bind_some { raw_flat; raw_perm; checked_perm; oldctx; newctx } ->
        let (Bplus raw_append) = Nbwd.bplus (Flatten.fwd_dom telf) in
        let (Bplus (new_flat, bplus_raw')) = Flatten.bplus Zero telf raw_append in
        let Eq = Fwn.bplus_uniq bplus_raw bplus_raw' in
        (* The N.perm_inv here is absolutely essential.  Our choice to index N.perm by a separate domain and codomain, even though in concrete cases the two are always equal, means that if we leave it off, the typechecker complains.  (We could convince the typechecker to let us leave it off by destructing "perm_eq", but that would be stupid.) *)
        let raw_perm =
          N.perm_inv
            (Flatten.permute raw_flat new_flat (Tbwd.append_append_permute raw_perm raw_append))
        in
        let Eq =
          Tctx.fwd_tgt_uniq (bcomp_permute_right checked_perm) (Tctx.bcomp_right checked_append)
        in
        let checked_perm = permute_bcomp_permute checked_perm checked_append in
        Bind_some { raw_perm; checked_perm; oldctx; newctx }
    | None -> None
end

(* Note the different return type of this bind_some and of Ordered.bind_some.  The latter returns a new ordered context and two permutations, one for the raw indices and one for the checked indices.  This one incorporates the raw permutation into the permutation stored in the context and returns only the checked permutation to the caller. *)
type (_, _, _) bind_some =
  | Bind_some : {
      checked_perm : ('c, 'b) permute;
      oldctx : ('mode, 'a, 'c) Ctx.t;
      newctx : ('mode, 'a, 'c) Ctx.t;
    }
      -> ('mode, 'a, 'b) bind_some
  | None : ('mode, 'a, 'b) bind_some

let bind_some g (Ctx.Permute { perm; ctx; level; _ }) =
  match Ordered.bind_some g ~level ctx with
  | Bind_some { raw_perm; checked_perm; oldctx; newctx } ->
      let perm = N.perm_comp perm raw_perm in
      Bind_some
        {
          checked_perm;
          oldctx =
            Permute
              {
                perm;
                env = Ctx.Ordered.env oldctx;
                level = Ctx.Ordered.length oldctx;
                ctx = oldctx;
              };
          newctx =
            Permute
              {
                perm;
                env = Ctx.Ordered.env newctx;
                level = Ctx.Ordered.length newctx;
                ctx = newctx;
              };
        }
  | None -> None
