open Signatures
open Tlist
open Tbwd
open Monoid

(* Type-level free monoids.  The type of generators is specified by a type family in a module parameter.  If there is exactly one generator, the result should be isomorphic to the type-level (backwards) natural numbers. *)

module Make (G : Permutable) = struct
  (* As the words themselves, we use type-level backwards lists (Tbwd) of generators. *)
  type zero = emp
  type ('n, 'g) suc = ('n, 'g) snoc

  (* ********** Addition ********** *)

  (* Addition is appending two words.  Note that this is different from bplus, below, which appends a *forwards* word on the right of a backwards one.  It also ensures that the appended list consists of valid generators. *)

  type (_, _, _) plus =
    | Zero : ('m, zero, 'm) plus
    | Suc : ('m, 'n, 'p) plus * 'g G.t -> ('m, ('n, 'g) suc, ('p, 'g) suc) plus

  (* Thus, as with natural numbers, a valid word is one that can be appended to something.  *)
  type _ t = Word : ('any, 'n, 'anyn) plus -> 'n t
  type wrapped = Wrap : 'n t -> wrapped

  let zero : zero t = Word Zero

  let suc : type n g. n t -> g G.t -> (n, g) suc t =
   fun n g ->
    match n with
    | Word n -> Word (Suc (n, g))

  let rec length : type n. n t -> int = function
    | Word Zero -> 0
    | Word (Suc (n, _)) -> 1 + length (Word n)

  type (_, _) has_plus = Plus : ('m, 'n, 'mn) plus -> ('m, 'n) has_plus

  let rec plus : type m n. n t -> (m, n) has_plus = function
    | Word Zero -> Plus Zero
    | Word (Suc (n, g)) ->
        let (Plus mn) = plus (Word n) in
        Plus (Suc (mn, g))

  let rec plus_out : type m n mn. m t -> (m, n, mn) plus -> mn t =
   fun pm mn ->
    match mn with
    | Zero -> pm
    | Suc (mn, g) ->
        let (Word p_mn) = plus_out pm mn in
        Word (Suc (p_mn, g))

  let plus_right : type m n mn. (m, n, mn) plus -> n t = fun mn -> Word mn

  let rec plus_left : type m n mn. (m, n, mn) plus -> mn t -> m t =
   fun p mn ->
    match (p, mn) with
    | Zero, _ -> mn
    | Suc (p, _), Word (Suc (mn, _)) -> plus_left p (Word mn)

  let rec plus_uniq : type m n mn mn'. (m, n, mn) plus -> (m, n, mn') plus -> (mn, mn') Eq.t =
   fun mn mn' ->
    match (mn, mn') with
    | Zero, Zero -> Eq
    | Suc (mn, _), Suc (mn', _) ->
        let Eq = plus_uniq mn mn' in
        Eq

  (* A plus with zero on the left is an equality. *)
  let rec zero_plus_uniq : type n p. (zero, n, p) plus -> (n, p) Eq.t = function
    | Zero -> Eq
    | Suc (p, _) ->
        let Eq = zero_plus_uniq p in
        Eq

  (* Shifting successors *)

  type (_, _, _, _) plus_suc =
    | Plus_suc :
        ((zero, 'g) suc, 'n, ('q, 'h) suc) plus * ('m, ('q, 'h) suc, 'p) plus
        -> ('m, 'g, 'n, 'p) plus_suc

  let rec plus_suc : type m n p g. g G.t -> ((m, g) suc, n, p) plus -> (m, g, n, p) plus_suc =
   fun g -> function
    | Zero -> Plus_suc (Zero, Suc (Zero, g))
    | Suc (x, h) ->
        let (Plus_suc (y, z)) = plus_suc g x in
        Plus_suc (Suc (y, h), Suc (z, h))

  (* Associativity *)

  let rec plus_assocl : type m n mn p np mnp.
      (m, n, mn) plus -> (n, p, np) plus -> (m, np, mnp) plus -> (mn, p, mnp) plus =
   fun mn np m_np ->
    match np with
    | Zero ->
        let Eq = plus_uniq mn m_np in
        Zero
    | Suc (np, _) ->
        let (Suc (m_np, g)) = m_np in
        let mn_p = plus_assocl mn np m_np in
        Suc (mn_p, g)

  let rec plus_assocr : type m n mn p np mnp.
      (m, n, mn) plus -> (n, p, np) plus -> (mn, p, mnp) plus -> (m, np, mnp) plus =
   fun mn np mn_p ->
    match np with
    | Zero ->
        let Zero = mn_p in
        mn
    | Suc (np, _) ->
        let (Suc (mn_p, g)) = mn_p in
        Suc (plus_assocr mn np mn_p, g)

  (* Unitality *)

  let rec zero_plus : type n. n t -> (zero, n, n) plus = function
    | Word Zero -> Zero
    | Word (Suc (n, g)) -> Suc (zero_plus (Word n), g)

  let plus_zero : type n. n t -> (n, zero, n) plus = fun _ -> Zero

  (* Addition in the free monoid on more than one generator is NOT commutative! *)

  (* ********** Commutation of words ********** *)

  (* A generator commutes with a word if it commutes with each generator in that word. *)
  type (_, _) gen_commute =
    | Commute_zero : ('g, zero) gen_commute
    | Commute_suc : ('g, 'n) gen_commute * ('g, 'h) G.commute -> ('g, ('n, 'h) suc) gen_commute

  let rec gen_commute : type g n. g G.t -> n t -> (g, n) gen_commute option =
   fun g -> function
    | Word Zero -> Some Commute_zero
    | Word (Suc (n, h)) -> (
        match gen_commute g (Word n) with
        | None -> None
        | Some gn -> (
            match G.commute g h with
            | Some gh -> Some (Commute_suc (gn, gh))
            | None -> None))

  (* Two words commute if each generator in one commutes with each generator in the other. *)
  type (_, _) commute =
    | Zero_commute : (zero, 'n) commute
    | Suc_commute : ('m, 'n) commute * ('g, 'n) gen_commute -> (('m, 'g) suc, 'n) commute

  let rec commute : type m n. m t -> n t -> (m, n) commute option =
   fun m n ->
    match m with
    | Word Zero -> Some Zero_commute
    | Word (Suc (m, g)) -> (
        match commute (Word m) n with
        | None -> None
        | Some mn -> (
            match gen_commute g n with
            | Some gn -> Some (Suc_commute (mn, gn))
            | None -> None))

  let rec commute_zero : type m. m t -> (m, zero) commute = function
    | Word Zero -> Zero_commute
    | Word (Suc (m, _)) -> Suc_commute (commute_zero (Word m), Commute_zero)

  let rec commute_suc : type m n g.
      m t -> g G.t -> (m, n) commute -> (g, m) gen_commute -> (m, (n, g) suc) commute =
   fun m g mn gm ->
    match mn with
    | Zero_commute -> Zero_commute
    | Suc_commute (mn, hn) ->
        let (Word (Suc (m, h))) = m in
        let (Commute_suc (gm, gh)) = gm in
        Suc_commute (commute_suc (Word m) g mn gm, Commute_suc (hn, G.commute_inv g h gh))

  let rec commute_inv : type m n. m t -> n t -> (m, n) commute -> (n, m) commute =
   fun m n -> function
    | Zero_commute -> commute_zero n
    | Suc_commute (mn, gn) ->
        let (Word (Suc (m, g))) = m in
        commute_suc n g (commute_inv (Word m) n mn) gn

  (* A word that commutes with another commutes with any of its own initial segments, and each of its generators commutes with the whole other word.  (For restricting the *other* word, see commute_uninsert and commute_plus_right below.) *)
  let commute_unsuc_left : type m n g. ((m, g) suc, n) commute -> (m, n) commute = function
    | Suc_commute (mn, _) -> mn

  let commute_gen : type m n g. ((m, g) suc, n) commute -> (g, n) gen_commute = function
    | Suc_commute (_, gn) -> gn

  (* ********** Centrality ********** *)

  (* A word is central if all of its generators are, i.e. if it commutes with every word whatsoever.  As with the words themselves, each step stores its generator, so that the word can be recovered from a centrality witness alone. *)
  type _ central =
    | Central_zero : zero central
    | Central_suc : 'n central * 'g G.t * 'g G.central -> ('n, 'g) suc central

  (* A central generator commutes with any word. *)
  let rec gen_commute_central : type g n. g G.t -> g G.central -> n t -> (g, n) gen_commute =
   fun g c -> function
    | Word Zero -> Commute_zero
    | Word (Suc (n, h)) -> Commute_suc (gen_commute_central g c (Word n), G.central_commute g h c)

  (* And hence a central word commutes with any word. *)
  let rec commute_central : type m n. m central -> n t -> (m, n) commute =
   fun c n ->
    match c with
    | Central_zero -> Zero_commute
    | Central_suc (c, g, gc) -> Suc_commute (commute_central c n, gen_commute_central g gc n)

  (* This is the operation that makes Word itself Permutable when its words are used as generators; the word being central is recoverable from the witness, so it is ignored. *)
  let central_commute : type m n. m t -> n t -> m central -> (m, n) commute =
   fun _ n c -> commute_central c n

  (* ********** Subwords ********** *)

  (* ('a, 'b) subword says that the word 'a is obtained from the word 'b by deleting some generators, the rest being kept in their original order.  Each step stores its generator, so that both words can be recovered from a subword alone. *)
  type (_, _) subword =
    | Sub_zero : (zero, zero) subword
    | Sub_keep : ('a, 'b) subword * 'g G.t -> (('a, 'g) suc, ('b, 'g) suc) subword
    | Sub_drop : ('a, 'b) subword * 'g G.t -> ('a, ('b, 'g) suc) subword

  let rec subword_in : type a b. (a, b) subword -> a t = function
    | Sub_zero -> zero
    | Sub_keep (s, g) -> suc (subword_in s) g
    | Sub_drop (s, _) -> subword_in s

  let rec subword_out : type a b. (a, b) subword -> b t = function
    | Sub_zero -> zero
    | Sub_keep (s, g) -> suc (subword_out s) g
    | Sub_drop (s, g) -> suc (subword_out s) g

  (* A generator that commutes with a word also commutes with any subword of it. *)
  let rec gen_commute_subword : type g a b.
      (a, b) subword -> (g, b) gen_commute -> (g, a) gen_commute =
   fun s gc ->
    match s with
    | Sub_zero -> Commute_zero
    | Sub_keep (s, _) ->
        let (Commute_suc (gc, c)) = gc in
        Commute_suc (gen_commute_subword s gc, c)
    | Sub_drop (s, _) ->
        let (Commute_suc (gc, _)) = gc in
        gen_commute_subword s gc

  (* Commutation restricts to the right-hand factors of sums. *)
  let rec gen_commute_plus_right : type g k l kl.
      (k, l, kl) plus -> (g, kl) gen_commute -> (g, l) gen_commute =
   fun kl gc ->
    match kl with
    | Zero -> Commute_zero
    | Suc (kl, _) ->
        let (Commute_suc (gc, c)) = gc in
        Commute_suc (gen_commute_plus_right kl gc, c)

  let rec commute_plus_right : type m n mn k l kl.
      (m, n, mn) plus -> (k, l, kl) plus -> (mn, kl) commute -> (n, l) commute =
   fun mn kl c ->
    match mn with
    | Zero -> Zero_commute
    | Suc (mn, _) ->
        let (Suc_commute (c, gc)) = c in
        Suc_commute (commute_plus_right mn kl c, gen_commute_plus_right kl gc)

  (* A generator commuting with the generators of a *forwards* word.  This is the forwards analogue of gen_commute. *)
  type (_, _) fwd_commute =
    | Fwd_commute_nil : ('g, nil) fwd_commute
    | Fwd_commute_cons :
        ('g, 'h) G.commute * ('g, 'b) fwd_commute
        -> ('g, ('h, 'b) cons) fwd_commute

  (* ********** Well-scoped De Bruijn indices ********** *)

  (* ('a, 'g, 'b) insert says that the word 'b is obtained by inserting the generator 'g somewhere in the word 'a.  Or, put differently, 'a is obtained from 'b by deleting a generator 'g in a specified location.  Thus it is also a well-scoped De Bruijn index into 'b, pointing at an occurrence of 'g.

     Since a word is only determined up to commutation of its generators, inserting 'g at a position other than the outer end means moving it past the generators outside that position.  Thus each Later step records a witness that 'g commutes with the generator it passes.  In particular, an insertion is exactly the datum of an equality (b = a·g) in the partially commutative monoid. *)
  type (_, _, _) insert =
    | Now : ('a, 'g, ('a, 'g) suc) insert
    | Later : ('g, 'k) G.commute * ('a, 'g, 'b) insert -> (('a, 'k) suc, 'g, ('b, 'k) suc) insert

  let rec int_of_insert : type a g b. (a, g, b) insert -> int = function
    | Now -> 0
    | Later (_, i) -> 1 + int_of_insert i

  (* Commutation also restricts along deletion of a generator from the right-hand word. *)
  let rec gen_commute_uninsert : type g m h n.
      (m, h, n) insert -> (g, n) gen_commute -> (g, m) gen_commute =
   fun i gc ->
    match i with
    | Now ->
        let (Commute_suc (gc, _)) = gc in
        gc
    | Later (_, i) ->
        let (Commute_suc (gc, c)) = gc in
        Commute_suc (gen_commute_uninsert i gc, c)

  (* And it commutes in particular with the generator at any given insertion position. *)
  let rec gen_commute_inserted : type g m h n.
      (m, h, n) insert -> (g, n) gen_commute -> (g, h) G.commute =
   fun i gc ->
    match i with
    | Now ->
        let (Commute_suc (_, c)) = gc in
        c
    | Later (_, i) ->
        let (Commute_suc (gc, _)) = gc in
        gen_commute_inserted i gc

  let rec commute_uninsert : type k m h n. (m, h, n) insert -> (k, n) commute -> (k, m) commute =
   fun i c ->
    match c with
    | Zero_commute -> Zero_commute
    | Suc_commute (c, gc) -> Suc_commute (commute_uninsert i c, gen_commute_uninsert i gc)

  (* Two successive insertions can be performed in the other order.  Swapping the order in which the two generators are inserted requires them to commute. *)
  type (_, _, _, _) comp_insert =
    | Comp_insert : ('a, 'k, 'd) insert * ('d, 'g, 'c) insert -> ('a, 'g, 'k, 'c) comp_insert

  let rec comp_insert : type a g k b c.
      (g, k) G.commute -> (a, g, b) insert -> (b, k, c) insert -> (a, g, k, c) comp_insert =
   fun gk ab bc ->
    match (ab, bc) with
    | Now, Now -> Comp_insert (Now, Later (gk, Now))
    | Now, Later (_, bc) -> Comp_insert (bc, Now)
    | Later (c, ab), Now -> Comp_insert (Now, Later (gk, Later (c, ab)))
    | Later (c, ab), Later (c', bc) ->
        let (Comp_insert (ad, dc)) = comp_insert gk ab bc in
        Comp_insert (Later (c', ad), Later (c, dc))

  let rec plus_insert : type a b c g ab ac.
      (a, b, ab) plus -> (a, c, ac) plus -> (b, g, c) insert -> (ab, g, ac) insert =
   fun ab ac i ->
    match i with
    | Now ->
        let (Suc (ac, _)) = ac in
        let Eq = plus_uniq ab ac in
        Now
    | Later (c, i) ->
        let Suc (ab, _), Suc (ac, _) = (ab, ac) in
        Later (c, plus_insert ab ac i)

  type (_, _, _, _) insert_plus =
    | Insert_plus : ('p, 'n, 'pn) plus * ('pn, 'g, 'mn) insert -> ('p, 'n, 'mn, 'g) insert_plus

  (* Extending an insertion by a word on the right moves the inserted generator past that whole word, so it must commute with all of it. *)
  let rec insert_plus : type m n mn g p.
      (g, n) gen_commute -> (p, g, m) insert -> (m, n, mn) plus -> (p, n, mn, g) insert_plus =
   fun gn i mn ->
    match (mn, gn) with
    | Zero, _ -> Insert_plus (Zero, i)
    | Suc (mn, g), Commute_suc (gn, gh) ->
        let (Insert_plus (pn, j)) = insert_plus gn i mn in
        Insert_plus (Suc (pn, g), Later (gh, j))

  (* If the inserted generator lies in the left factor, then it has to move past the whole right factor to reach the outer end, so the insertion's own witnesses tell us it commutes with all of that. *)
  type (_, _, _, _) insert_in_plus =
    | Left :
        ('pred_m, 'g, 'm) insert * ('pred_m, 'n, 'pred_mn) plus * ('g, 'n) gen_commute
        -> ('g, 'm, 'n, 'pred_mn) insert_in_plus
    | Right :
        ('pred_n, 'g, 'n) insert * ('m, 'pred_n, 'pred_mn) plus
        -> ('g, 'm, 'n, 'pred_mn) insert_in_plus

  let rec insert_in_plus : type m n g pred_mn mn.
      (m, n, mn) plus -> (pred_mn, g, mn) insert -> (g, m, n, pred_mn) insert_in_plus =
   fun mn i ->
    match mn with
    | Zero -> Left (i, Zero, Commute_zero)
    | Suc (mn, g) -> (
        match i with
        | Now -> Right (Now, mn)
        | Later (c, i) -> (
            match insert_in_plus mn i with
            | Left (j, pred_mn, gn) -> Left (j, Suc (pred_mn, g), Commute_suc (gn, c))
            | Right (k, pred_mn) -> Right (Later (c, k), Suc (pred_mn, g))))

  type (_, _, _, _) insert_into_plus =
    | Left :
        ('m, 'g, 'msuc) insert * ('msuc, 'n, 'mn_suc) plus
        -> ('g, 'm, 'n, 'mn_suc) insert_into_plus
    | Right :
        ('n, 'g, 'suc) insert * ('m, 'suc, 'mn_suc) plus
        -> ('g, 'm, 'n, 'mn_suc) insert_into_plus

  let rec insert_into_plus : type g m n mn mn_suc.
      g G.t -> (m, n, mn) plus -> (mn, g, mn_suc) insert -> (g, m, n, mn_suc) insert_into_plus =
   fun g mn i ->
    match i with
    | Now -> Right (Now, Suc (mn, g))
    | Later (c, i') -> (
        match mn with
        | Zero -> Left (Later (c, i'), Zero)
        | Suc (mn, h) -> (
            match insert_into_plus g mn i' with
            | Left (j, mn_suc) -> Left (j, Suc (mn_suc, h))
            | Right (k, mn_suc) -> Right (Later (c, k), Suc (mn_suc, h))))

  (* Two insertions into nested words can be performed in the other order, but as with comp_insert, this means moving the two inserted generators past each other, so they must commute. *)
  type (_, _, _, _) swap_inserts =
    | Swap_inserts : ('q, 'l, 'm) insert * ('p, 'k, 'q) insert -> ('m, 'k, 'l, 'p) swap_inserts

  let rec swap_inserts : type m n p k l.
      (l, k) G.commute -> (n, k, m) insert -> (p, l, n) insert -> (m, k, l, p) swap_inserts =
   fun lk k l ->
    match k with
    | Now -> Swap_inserts (Later (lk, l), Now)
    | Later (ck, k') -> (
        match l with
        | Now -> Swap_inserts (Now, k')
        | Later (cl, l') ->
            let (Swap_inserts (l'', k'')) = swap_inserts lk k' l' in
            Swap_inserts (Later (cl, l''), Later (ck, k'')))

  type (_, _, _) compare_inserts =
    | Eq_inserts : ('m, 'g, 'm) compare_inserts
    | Neq_inserts : ('r, 'g, 'm) insert * ('r, 'g, 'n) insert -> ('m, 'g, 'n) compare_inserts

  let rec compare_inserts : type m n g p.
      (m, g, p) insert -> (n, g, p) insert -> (m, g, n) compare_inserts =
   fun m n ->
    match (m, n) with
    | Now, Now -> Eq_inserts
    | Now, Later (_, m) -> Neq_inserts (m, Now)
    | Later (_, n), Now -> Neq_inserts (Now, n)
    | Later (cm, m), Later (cn, n) -> (
        match compare_inserts m n with
        | Eq_inserts -> Eq_inserts
        | Neq_inserts (m', n') -> Neq_inserts (Later (cm, m'), Later (cn, n')))

  (* Compare two insertions into the same word whose removed elements may have different generator types.  If they remove the same position, the generators and smaller words agree; otherwise each insert transfers to the other's smaller word.  In the latter case the two generators are inserted at different places, so whichever is inserted further in passes the other one, and hence they commute; we report both orientations of that witness, since we know both generators. *)
  type (_, _, _, _, _) compare_gen_inserts =
    | Eq_gen_inserts : ('a, 'g, 'a, 'g, 'p) compare_gen_inserts
    | Neq_gen_inserts :
        ('r, 'h, 'a) insert * ('r, 'g, 'b) insert * ('g, 'h) G.commute * ('h, 'g) G.commute
        -> ('a, 'g, 'b, 'h, 'p) compare_gen_inserts

  let rec compare_gen_inserts : type a g b h p.
      g G.t -> h G.t -> (a, g, p) insert -> (b, h, p) insert -> (a, g, b, h, p) compare_gen_inserts
      =
   fun g h j k ->
    match (j, k) with
    | Now, Now -> Eq_gen_inserts
    | Now, Later (c, k) -> Neq_gen_inserts (k, Now, G.commute_inv h g c, c)
    | Later (c, j), Now -> Neq_gen_inserts (Now, j, c, G.commute_inv g h c)
    | Later (cj, j), Later (ck, k) -> (
        match compare_gen_inserts g h j k with
        | Eq_gen_inserts -> Eq_gen_inserts
        | Neq_gen_inserts (k', j', gh, hg) ->
            Neq_gen_inserts (Later (ck, k'), Later (cj, j'), gh, hg))

  (* Two insertions of the same generator into the same word are equal exactly when they insert it in the same place, in which case their outputs agree. *)
  let rec insert_equal : type a g b1 b2.
      (a, g, b1) insert -> (a, g, b2) insert -> (b1, b2) Eq.compare =
   fun i1 i2 ->
    match (i1, i2) with
    | Now, Now -> Eq
    | Later (_, i1), Later (_, i2) -> (
        match insert_equal i1 i2 with
        | Eq -> Eq
        | Neq -> Neq)
    | _ -> Neq

  let rec insert_equiv : type m n g p q. (p, g, m) insert -> (q, g, n) insert -> unit option =
   fun k l ->
    match (k, l) with
    | Now, Now -> Some ()
    | Later (_, k), Later (_, l) -> insert_equiv k l
    | _, _ -> None

  type _ insert_into = Into : 'g G.t * ('m, 'g, 'msuc) insert -> 'msuc insert_into

  (* A generator can only be inserted at positions past which it commutes, so the deeper insertions are filtered by commutation with the generators they pass. *)
  let rec all_inserts : type n. n t -> n insert_into Seq.t = function
    | Word Zero -> Seq.empty
    | Word (Suc (n, g)) ->
        Seq.cons
          (Into (g, Now))
          (Seq.filter_map
             (fun (Into (h, k)) ->
               match G.commute h g with
               | Some c -> Some (Into (h, Later (c, k)))
               | None -> None)
             (all_inserts (Word n)))

  let rec compare : type m n. m t -> n t -> (m, n) Eq.compare =
   fun m n ->
    match (m, n) with
    | Word Zero, Word Zero -> Eq
    | Word Zero, Word (Suc (_, _)) -> Neq
    | Word (Suc (_, _)), Word Zero -> Neq
    | Word (Suc (m, g)), Word (Suc (n, h)) -> (
        match compare (Word m) (Word n) with
        | Neq -> Neq
        | Eq -> (
            match G.compare g h with
            | Eq -> Eq
            | Neq -> Neq))

  (* Strip the leftmost generator from a [((m, g) suc, n, p) plus]: returns the inner [(m, n, p_inner) plus] and an insertion that recovers p as p_inner with g inserted at the appropriate position. *)
  type (_, _, _, _) strip_plus_left =
    | Strip_plus_left : ('m, 'n, 'q) plus * ('q, 'g, 'p) insert -> ('m, 'g, 'n, 'p) strip_plus_left

  (* Stripping the leftmost generator moves it past the whole word appended to it, so it must commute with all of that. *)
  let rec strip_plus_left : type m g n p.
      (g, n) gen_commute -> g G.t -> ((m, g) suc, n, p) plus -> (m, g, n, p) strip_plus_left =
   fun gn g ab ->
    match (ab, gn) with
    | Zero, _ -> Strip_plus_left (Zero, Now)
    | Suc (ab, h), Commute_suc (gn, gh) ->
        let (Strip_plus_left (q, i)) = strip_plus_left gn g ab in
        Strip_plus_left (Suc (q, h), Later (gh, i))

  (* ********** More about insertion ********** *)

  let rec insert : type a n b. (a, n, b) insert -> a t -> n G.t -> b t =
   fun i (Word a) n ->
    match i with
    | Now -> Word (Suc (a, n))
    | Later (_, i) ->
        let (Suc (a, k)) = a in
        let (Word ins) = insert i (Word a) n in
        Word (Suc (ins, k))

  let rec uninsert : type a n b. (a, n, b) insert -> b t -> a t =
   fun i b ->
    match i with
    | Now ->
        let (Word (Suc (b, _))) = b in
        Word b
    | Later (_, i) ->
        let (Word (Suc (b, n))) = b in
        let (Word ins) = uninsert i (Word b) in
        Word (Suc (ins, n))

  let rec inserted : type a n b. (a, n, b) insert -> b t -> n G.t =
   fun i b ->
    match i with
    | Now ->
        let (Word (Suc (_, n))) = b in
        n
    | Later (_, i) ->
        let (Word (Suc (b, _))) = b in
        inserted i (Word b)

  (* ********** Permutations ********** *)

  (* A free monoid is not commutative, but it is the object set of a free symmetric strict monoidal category.  Here are the morphisms in that category: ('m, 'n) permute is a permutation with domain the word 'm and codomain the word 'n.  Like a degeneracy (see Dim.Deg, whose definition this deliberately matches, since every permutation of dimensions is a degeneracy), a permutation is defined inductively by insertion: the codomain grows on the right by a generator, and the domain records with an insert where the preimage of that generator lies in it.  As with degeneracies, each step stores its generator, so that both the domain and the codomain can be recovered from a permutation alone. *)
  type (_, _) permute =
    | Zero : (zero, zero) permute
    | Suc : ('a, 'b) permute * 'g G.t * ('a, 'g, 'c) insert -> ('c, ('b, 'g) suc) permute

  let rec perm_dom : type m n. (m, n) permute -> m t = function
    | Zero -> zero
    | Suc (p, g, i) -> insert i (perm_dom p) g

  let rec perm_cod : type m n. (m, n) permute -> n t = function
    | Zero -> zero
    | Suc (p, g, _) -> suc (perm_cod p) g

  let rec perm_id : type a. a t -> (a, a) permute = function
    | Word Zero -> Zero
    | Word (Suc (a, g)) -> Suc (perm_id (Word a), g, Now)

  (* A permutation is the identity exactly when every element is inserted at the far end. *)
  let rec perm_is_id : type m n. (m, n) permute -> (m, n) Eq.compare = function
    | Zero -> Eq
    | Suc (p, _, i) -> (
        match perm_is_id p with
        | Neq -> Neq
        | Eq -> (
            match i with
            | Now -> Eq
            | Later _ -> Neq))

  (* By "residual" of a permutation, given an element of its codomain, we mean the preimage of that element together with the permutation obtained by removing that element from the codomain and its preimage from the domain. *)
  type (_, _, _) perm_residual =
    | Residual : ('m, 'n) permute * 'g G.t * ('m, 'g, 'msuc) insert -> ('msuc, 'n, 'g) perm_residual

  let rec perm_residual : type m n g npred.
      (m, n) permute -> (npred, g, n) insert -> (m, npred, g) perm_residual =
   fun s k ->
    match (k, s) with
    | Now, Suc (s, g, i) -> Residual (s, g, i)
    (* The generator we are removing from the codomain is not the outermost one, so it must pass the outermost one; the insert tells us they commute, which is exactly what is needed to swap their preimages in the domain. *)
    | Later (c, k), Suc (s, g, i) ->
        let (Residual (s, g', j)) = perm_residual s k in
        let (Swap_inserts (i, j)) = swap_inserts c i j in
        Residual (Suc (s, g, j), g', i)

  (* Dually, by "coresidual" of a permutation, given an element of its domain, we mean the image of that element together with the permutation obtained by removing that element from the domain and its image from the codomain.  Unlike a degeneracy, a permutation always has such an image. *)
  type (_, _, _) perm_coresidual =
    | Coresidual :
        ('mpred, 'npred) permute * ('npred, 'g, 'n) insert
        -> ('mpred, 'g, 'n) perm_coresidual

  (* We need to be told the generator being removed, since to place its image in the codomain we may have to move it past the outermost generator there, and the witness that they commute is only available in one orientation. *)
  let rec perm_coresidual : type mpred g m n.
      g G.t -> (m, n) permute -> (mpred, g, m) insert -> (mpred, g, n) perm_coresidual =
   fun h s k ->
    match s with
    | Zero -> (
        match k with
        | _ -> .)
    | Suc (s, g, j) -> (
        match compare_gen_inserts g h j k with
        | Eq_gen_inserts -> Coresidual (s, Now)
        | Neq_gen_inserts (k, j, _, hg) ->
            let (Coresidual (s, i)) = perm_coresidual h s k in
            Coresidual (Suc (s, g, j), Later (hg, i)))

  (* Using residuals, we can compose permutations. *)
  let rec perm_comp : type a b c. (a, b) permute -> (b, c) permute -> (a, c) permute =
   fun ab bc ->
    match bc with
    | Zero ->
        let Zero = ab in
        Zero
    | Suc (s, _, k) ->
        let (Residual (t, g', i)) = perm_residual ab k in
        Suc (perm_comp t s, g', i)

  (* To invert permutations, we first define the dual of Suc that adds a generator to the domain and inserts it anywhere in the codomain. *)
  let rec coinsert : type m n g nsuc.
      (m, n) permute -> g G.t -> (n, g, nsuc) insert -> ((m, g) suc, nsuc) permute =
   fun p g -> function
    | Now -> Suc (p, g, Now)
    (* The new generator is inserted inside the outermost generator of the codomain, so in the domain, where it is outermost, the preimage of that generator must move past it instead. *)
    | Later (c, i) ->
        let (Suc (p, h, j)) = p in
        Suc (coinsert p g i, h, Later (G.commute_inv g h c, j))

  let rec perm_inv : type m n. (m, n) permute -> (n, m) permute = function
    | Zero -> Zero
    | Suc (p, g, i) -> coinsert (perm_inv p) g i

  let rec insert_of_plus : type b a ba bga g.
      (g, a) gen_commute -> (b, a, ba) plus -> ((b, g) suc, a, bga) plus -> (ba, g, bga) insert =
   fun ga ba bga ->
    match (ba, bga, ga) with
    | Zero, Zero, _ -> Now
    | Suc (ba, _), Suc (bga, _), Commute_suc (ga, gh) -> Later (gh, insert_of_plus ga ba bga)

  (* Two words can be swapped past each other with a permutation, provided of course that they commute. *)
  let rec perm_swap : type a b ab ba.
      (a, b) commute -> (a, b, ab) plus -> (b, a, ba) plus -> (ab, ba) permute =
   fun c ab ba ->
    match ba with
    | Zero ->
        let b = plus_right ab in
        let Eq = plus_uniq ab (zero_plus b) in
        perm_id b
    | Suc (ba, g) ->
        let (Plus ab') = plus (plus_right ab) in
        Suc (perm_swap (commute_unsuc_left c) ab' ba, g, insert_of_plus (commute_gen c) ab' ab)

  (* Extend a permutation by the identity on an additional word. *)
  let rec perm_plus : type m n k mk nk.
      (m, n) permute -> (n, k, nk) plus -> (m, k, mk) plus -> (mk, nk) permute =
   fun s nk mk ->
    match (nk, mk) with
    | Zero, Zero -> s
    | Suc (nk, g), Suc (mk, _) -> Suc (perm_plus s nk mk, g, Now)

  (* Two permutations can be placed side by side. *)
  let rec perm_plus_perm : type a b ab c d cd.
      (a, c) permute -> (a, b, ab) plus -> (c, d, cd) plus -> (b, d) permute -> (ab, cd) permute =
   fun p ab cd q ->
    match q with
    | Zero ->
        let Zero = cd in
        let Zero = ab in
        p
    | Suc (q, g, i) ->
        let (Suc (cd', _)) = cd in
        let (Plus ab') = plus (perm_dom q) in
        Suc (perm_plus_perm p ab' cd' q, g, plus_insert ab' ab i)

  (* ********** Subtraction ********** *)

  let rec minus : type m n mn. mn t -> (m, n, mn) plus -> m t =
   fun mn n ->
    match (mn, n) with
    | mn, Zero -> mn
    | Word (Suc (mn, _)), Suc (n, _) -> minus (Word mn) n

  let rec minus_uniq : type m1 m2 n mn. (m1, n, mn) plus -> (m2, n, mn) plus -> (m1, m2) Eq.t =
   fun n1 n2 ->
    match (n1, n2) with
    | Zero, Zero -> Eq
    | Suc (n1, _), Suc (n2, _) -> minus_uniq n1 n2

  let rec plus_suc_neq : type m n g c. g G.t -> (m, (n, g) suc, m) plus -> c =
   fun g -> function
    | Suc (mn, _) -> suc_plus_neq g mn

  and suc_plus_neq : type m n g c. g G.t -> ((m, g) suc, n, m) plus -> c =
   fun g mm ->
    let (Plus_suc (_, y)) = plus_suc g mm in
    let (Suc (_, h)) = y in
    plus_suc_neq h y

  let rec minus_uniq' : type m n1 n2 mn.
      m t -> (m, n1, mn) plus -> (m, n2, mn) plus -> (n1, n2) Eq.t =
   fun m n1 n2 ->
    match (n1, n2) with
    | Zero, Zero -> Eq
    | Suc (n1, _), Suc (n2, _) ->
        let Eq = minus_uniq' m n1 n2 in
        Eq
    | Zero, Suc (_, g) -> plus_suc_neq g n2
    | Suc (_, g), Zero -> plus_suc_neq g n1

  (* ********** Forwards words ********** *)

  type 'b fwd = Nil : nil fwd | Cons : 'n G.t * 'b fwd -> ('n, 'b) cons fwd
  type fwd_zero = nil

  let fwd_zero : fwd_zero fwd = Nil

  (* As with lists and backwards lists, a forwards word can naturally be appended to a backwards one. *)
  type (_, _, _) bplus =
    | Append_nil : ('a, nil, 'a) bplus
    | Append_cons : (('a, 'x) suc, 'b, 'c) bplus -> ('a, ('x, 'b) cons, 'c) bplus

  type (_, _) has_bplus = Bplus : ('a, 'b, 'ab) bplus -> ('a, 'b) has_bplus

  let rec bplus : type a b. b fwd -> (a, b) has_bplus = function
    | Nil -> Bplus Append_nil
    | Cons (_, b) ->
        let (Bplus ab) = bplus b in
        Bplus (Append_cons ab)

  (* The generators of a forwards word are irrelevant to computing a bplus, so a Tlist of them suffices. *)
  let rec bplus_of_tlist : type a b. b Tlist.t -> (a, b) has_bplus = function
    | Nil -> Bplus Append_nil
    | Cons xs ->
        let (Bplus ab) = bplus_of_tlist xs in
        Bplus (Append_cons ab)

  type _ to_fwd = To_fwd : 'a fwd * (emp, 'a, 'b) bplus -> 'b to_fwd

  let to_fwd : type c. c t -> c to_fwd =
   fun c ->
    let rec go : type a b c. a t -> b fwd -> (a, b, c) bplus -> c to_fwd =
     fun a b abc ->
      match a with
      | Word Zero -> To_fwd (b, abc)
      | Word (Suc (a, x)) -> go (Word a) (Cons (x, b)) (Append_cons abc) in
    go c Nil Append_nil

  let rec bplus_right : type a b ab. (a, b, ab) bplus -> b Tlist.t = function
    | Append_nil -> Nil
    | Append_cons ab -> Cons (bplus_right ab)

  let rec bplus_uniq : type a b ab ab'. (a, b, ab) bplus -> (a, b, ab') bplus -> (ab, ab') Eq.t =
   fun ab ab' ->
    match (ab, ab') with
    | Append_nil, Append_nil -> Eq
    | Append_cons ab, Append_cons ab' ->
        let Eq = bplus_uniq ab ab' in
        Eq

  (* Transferring an insertion across an appended forwards word moves the inserted generator past all of that word, so it must commute with it. *)
  let rec insert_bplus : type a asuc g b ab asucb.
      (g, b) fwd_commute ->
      (a, g, asuc) insert ->
      (a, b, ab) bplus ->
      (asuc, b, asucb) bplus ->
      (ab, g, asucb) insert =
   fun gb i ab asucb ->
    match (ab, asucb, gb) with
    | Append_nil, Append_nil, _ -> i
    | Append_cons ab, Append_cons asucb, Fwd_commute_cons (gh, gb) ->
        insert_bplus gb (Later (gh, i)) ab asucb

  (* Pulling a generator out of a forwards word and moving it to the front, past the generators that precede it there.  This is Tlist.insert decorated with the witnesses that those moves are allowed. *)
  type (_, _, _) fwd_insert =
    | Fwd_now : ('g, 'b, ('g, 'b) cons) fwd_insert
    | Fwd_later :
        ('g, 'h) G.commute * ('g, 'b, 'd) fwd_insert
        -> ('g, ('h, 'b) cons, ('h, 'd) cons) fwd_insert

  (* The generator inserted at a given position of a forwards word, and the word with it removed. *)
  let rec fwd_inserted : type a g b. (g, a, b) fwd_insert -> b fwd -> g G.t =
   fun i b ->
    match (i, b) with
    | Fwd_now, Cons (g, _) -> g
    | Fwd_later (_, i), Cons (_, b) -> fwd_inserted i b

  let rec fwd_uninsert : type a g b. (g, a, b) fwd_insert -> b fwd -> a fwd =
   fun i b ->
    match (i, b) with
    | Fwd_now, Cons (_, b) -> b
    | Fwd_later (_, i), Cons (g, b) -> Cons (g, fwd_uninsert i b)

  let rec fwd_insert_tlist : type a g b. (g, a, b) fwd_insert -> a Tlist.t -> b Tlist.t =
   fun i a ->
    match i with
    | Fwd_now -> Cons a
    | Fwd_later (_, i) ->
        let (Cons a) = a in
        Cons (fwd_insert_tlist i a)

  (* Extend a permutation by the identity on an appended forwards word.  This is perm_plus for bplus rather than plus, and like it needs the generators of the appended word to grow the codomain. *)
  let rec perm_bplus : type a b c ac bc.
      c fwd -> (a, b) permute -> (a, c, ac) bplus -> (b, c, bc) bplus -> (ac, bc) permute =
   fun c p ac bc ->
    match (c, ac, bc) with
    | Nil, Append_nil, Append_nil -> p
    | Cons (g, c), Append_cons ac, Append_cons bc -> perm_bplus c (Suc (p, g, Now)) ac bc

  (* When appending a forwards word to a backwards one, if we insert the same generator on the left and on the right, the results are permuted.  The forwards word passed is the one *containing* the inserted generator, so that it supplies both that generator and those of the part appended after it. *)
  let rec perm_of_ins_ins : type a b g c d ad bc.
      a t ->
      d fwd ->
      (a, g, b) insert ->
      (g, c, d) fwd_insert ->
      (b, c, bc) bplus ->
      (a, d, ad) bplus ->
      (bc, ad) permute =
   fun a d ab cd bc ad' ->
    match (cd, d) with
    | Fwd_now, Cons (g, c) ->
        let (Append_cons ad') = ad' in
        perm_bplus c (Suc (perm_id a, g, ab)) bc ad'
    (* Appending the generator on the left of h instead of on the right of it requires them to commute, which is exactly what the fwd_insert records. *)
    | Fwd_later (gh, cd), Cons (h, d) ->
        let Append_cons ad', Append_cons bc = (ad', bc) in
        perm_of_ins_ins (suc a h) d (Later (gh, ab)) cd bc ad'

  (* ('a, 'b, 'c) bplus_permute says that the backwards word 'c is obtained from the backwards word 'a by appending a permutation of the forwards word 'b.  In particular, (zero, 'b, 'c) says that the backwards word 'c is a permutation of the forwards word 'b. *)
  type (_, _, _) bplus_permute =
    | Bp_nil : ('a, nil, 'a) bplus_permute
    | Bp_insert :
        ('g, 'b, 'd) fwd_insert * (('a, 'g) suc, 'b, 'c) bplus_permute
        -> ('a, 'd, 'c) bplus_permute

  let rec bplus_permute_right : type a b c. (a, b, c) bplus_permute -> b Tlist.t = function
    | Bp_nil -> Nil
    | Bp_insert (ins, b) -> fwd_insert_tlist ins (bplus_permute_right b)

  (* If we bplus and also bplus_permute the same words, the two results are related by a permutation.  Since permutations record their generators, we need the backwards word being appended to and the generators of the forwards word appended. *)
  let rec perm_of_bplus_permute : type a b c d.
      a t -> b fwd -> (a, b, d) bplus_permute -> (a, b, c) bplus -> (d, c) permute =
   fun a b d c ->
    match d with
    | Bp_nil ->
        let Append_nil = c in
        perm_id a
    | Bp_insert (ins, d) ->
        let g = fwd_inserted ins b in
        let (Bplus a') = bplus_of_tlist (bplus_permute_right d) in
        let perm1 = perm_of_bplus_permute (suc a g) (fwd_uninsert ins b) d a' in
        let perm2 = perm_of_ins_ins a b Now ins a' c in
        perm_comp perm1 perm2

  (* Concatenation of two *forwards* words: (a, b, ab) fplus means the forwards word ab is a followed by b. *)
  type (_, _, _) fplus =
    | Nil : (nil, 'b, 'b) fplus
    | Cons : ('a, 'b, 'ab) fplus -> (('g, 'a) cons, 'b, ('g, 'ab) cons) fplus

  (* Appending two forwards words onto a backwards word, one after the other, is the same as appending their concatenation.  This is just associativity of word concatenation, so it holds for any generators. *)
  let rec bplus_bplus : type z a za b ab zab.
      (z, a, za) bplus -> (za, b, zab) bplus -> (a, b, ab) fplus -> (z, ab, zab) bplus =
   fun za zab fp ->
    match fp with
    | Nil ->
        let Append_nil = za in
        zab
    | Cons fp ->
        let (Append_cons za) = za in
        Append_cons (bplus_bplus za zab fp)

  (* Conversely, if we know how to append a concatenation, we can strip off the second factor. *)
  let rec unbplus_bplus : type z a b ab zab.
      (z, ab, zab) bplus -> (a, b, ab) fplus -> (z, a) has_bplus =
   fun zab fp ->
    match fp with
    | Nil -> Bplus Append_nil
    | Cons fp ->
        let (Append_cons zab) = zab in
        let (Bplus za) = unbplus_bplus zab fp in
        Bplus (Append_cons za)

  (* Prepending a *backwards* word to a *forwards* one, giving a forwards word: (a, b, ab) bfplus means the forwards word ab is the backwards word a followed by the forwards word b.  Analogous to Fwn.fplus.  As with that, the induction moves generators one at a time from the inner (snoc) end of a to the head (cons) of b. *)
  type (_, _, _) bfplus =
    | Zero : (emp, 'b, 'b) bfplus
    | Suc : ('a, ('g, 'b) cons, 'ab) bfplus -> (('a, 'g) snoc, 'b, 'ab) bfplus

  type (_, _) has_bfplus = Bfplus : 'ab fwd * ('a, 'b, 'ab) bfplus -> ('a, 'b) has_bfplus

  let rec bfplus : type a b. a t -> b fwd -> (a, b) has_bfplus =
   fun a b ->
    match a with
    | Word Zero -> Bfplus (b, Zero)
    | Word (Suc (a, g)) ->
        let (Bfplus (ab, bfp)) = bfplus (Word a) (Cons (g, b)) in
        Bfplus (ab, Suc bfp)

  (* ********** Positive words ********** *)

  (* A "positive" word is one that's not the identity, i.e. is a successor of something. *)

  type _ pos = Pos : 'n t * 'g G.t -> ('n, 'g) suc pos

  let zero_nonpos : type c. zero pos -> c = function
    | _ -> .

  let plus_pos : type a b ab. a t -> b pos -> (a, b, ab) plus -> ab pos =
   fun a b ab ->
    let (Pos _) = b in
    let (Suc (ab, g)) = ab in
    Pos (plus_out a ab, g)

  let pos_plus : type a b ab. a pos -> (a, b, ab) plus -> ab pos =
   fun (Pos (a, g)) ab ->
    let (Plus_suc (_, Suc (ab, h))) = plus_suc g ab in
    Pos (plus_out a ab, h)

  let rec insert_pos : type m g n. m t -> g G.t -> (m, g, n) insert -> n pos =
   fun m g i ->
    match i with
    | Now -> Pos (m, g)
    | Later (_, i) ->
        let (Word (Suc (m, h))) = m in
        let (Pos (mi, k)) = insert_pos (Word m) g i in
        Pos (suc mi k, h)

  let pos : type a. a pos -> a t = fun (Pos (Word a, g)) -> Word (Suc (a, g))

  (* A permutation of a positive word has positive domain. *)
  let perm_pos : type m n. n pos -> (m, n) permute -> m pos =
   fun n s ->
    match (n, s) with
    | Pos _, Suc (s, g, i) -> insert_pos (perm_dom s) g i

  type _ compare_zero = Zero : zero compare_zero | Pos : 'n pos -> 'n compare_zero

  let compare_zero : type a. a t -> a compare_zero = function
    | Word Zero -> Zero
    | Word (Suc (a, g)) -> Pos (Pos (Word a, g))

  (* ********** Factoring ********** *)

  type (_, _) factor = Factor : ('n, 'k, 'nk) plus -> ('nk, 'n) factor

  (* This is a hot path: it is called from pushout, and thence from Deg.comp_deg_extending, many millions of times in higher-dimensional normalization.  So we match on the option explicitly rather than going through Monad.Maybe, whose let* allocates a closure at every level of the recursion. *)
  let rec factor : type nk n. nk t -> n t -> (nk, n) factor option =
   fun nk n ->
    match compare nk n with
    | Eq -> Some (Factor Zero)
    | Neq -> (
        match nk with
        | Word Zero -> None
        | Word (Suc (nk, g)) -> (
            match factor (Word nk) n with
            | Some (Factor n_k) -> Some (Factor (Suc (n_k, g)))
            | None -> None))

  type (_, _) cofactor = Cofactor : ('n, 'k, 'nk) plus -> ('nk, 'k) cofactor

  let rec cofactor : type nk k. nk t -> k t -> (nk, k) cofactor option =
   fun nk k ->
    match (nk, k) with
    | Word Zero, Word Zero -> Some (Cofactor Zero)
    | Word (Suc (nk, g)), Word (Suc (k, h)) -> (
        match G.compare g h with
        | Eq -> (
            match cofactor (Word nk) (Word k) with
            | Some (Cofactor n) -> Some (Cofactor (Suc (n, g)))
            | None -> None)
        | Neq -> None)
    | Word (Suc _), Word Zero -> Some (Cofactor (plus_zero nk))
    | _ -> None

  (* Trichotomy.  With multiple generators, two words need not be comparable, so there is a fourth case. *)

  type (_, _) trichotomy =
    | Eq : ('n, 'n) trichotomy
    | Lt : ('m, ('n, 'g) suc, 'mn) plus -> ('m, 'mn) trichotomy
    | Gt : ('m, ('n, 'g) suc, 'mn) plus -> ('mn, 'm) trichotomy
    | Incomparable : ('m, 'n) trichotomy

  let trichotomy : type m n. m t -> n t -> (m, n) trichotomy =
   fun m n ->
    match factor m n with
    | Some (Factor Zero) -> Eq
    | Some (Factor (Suc _ as k)) -> Gt k
    | _ -> (
        match factor n m with
        | Some (Factor Zero) -> Eq
        | Some (Factor (Suc _ as k)) -> Lt k
        | _ -> Incomparable)

  type (_, _) pushout = Pushout : ('a, 'c, 'p) plus * ('b, 'd, 'p) plus -> ('a, 'b) pushout

  (* Building the pair (factor a b, factor b a) evaluated both factorizations even when only the first branch was taken.  Testing them in the order the branches consume them avoids that; measured effect is small (~0.5%), since the redundant call is usually cheap. *)
  let pushout : type a b. a t -> b t -> (a, b) pushout =
   fun a b ->
    match factor b a with
    | Some (Factor ab) -> Pushout (ab, Zero)
    | None -> (
        match factor a b with
        | Some (Factor ba) -> Pushout (Zero, ba)
        | None -> raise (Failure "Word.pushout"))
end

module MakeCheck (G : Permutable) : Monoid = Make (G)
module MakeCheckPos (G : Permutable) : MonoidPos = Make (G)
module MakeCheckPerm (G : Permutable) : MonoidPerm = Make (G)

module type PermutableExp = sig
  include Permutable

  type ('g, 'n) endpoints
  type _ has_endpoints = Endpoints : ('g, 'n) endpoints -> 'g has_endpoints

  val endpoints_in : ('g, 'n) endpoints -> 'g t
  val endpoints_out : ('g, 'n) endpoints -> 'n N.t
  val has_endpoints : 'g t -> 'g has_endpoints
  val endpoints_uniq : ('g, 'n1) endpoints -> ('g, 'n2) endpoints -> ('n1, 'n2) Eq.t
end

(* ********** Occurrence ********** *)

module MakeDecidable (G : DecidablePermutable) = struct
  include Make (G)

  (* Whether a generator occurs in a word.  This is a purely positional statement, unlike an insert, which also requires the generator to commute with everything outside its position. *)
  type (_, _) occurs =
    | Occurs_now : ('g, ('m, 'g) suc) occurs
    | Occurs_later : ('g, 'm) occurs -> ('g, ('m, 'h) suc) occurs

  type (_, _) unoccurs =
    | Unoccurs_emp : ('g, emp) unoccurs
    | Unoccurs_suc : ('g, 'm) unoccurs * ('g, 'h) G.apart -> ('g, ('m, 'h) suc) unoccurs

  let rec occurs : type g m. g G.t -> m t -> ((g, m) occurs, (g, m) unoccurs) Either.t =
   fun g -> function
    | Word Zero -> Right Unoccurs_emp
    | Word (Suc (m, h)) -> (
        match G.decide g h with
        | Same -> Left Occurs_now
        | Distinct ap -> (
            match occurs g (Word m) with
            | Left o -> Left (Occurs_later o)
            | Right u -> Right (Unoccurs_suc (u, ap))))

  let rec occurs_unoccurs : type g m r. (g, m) occurs -> (g, m) unoccurs -> r =
   fun o u ->
    match (o, u) with
    | Occurs_now, Unoccurs_suc (_, ap) -> (
        match G.apart_irrefl ap with
        | _ -> .)
    | Occurs_later o, Unoccurs_suc (u, _) -> occurs_unoccurs o u

  let rec occurs_plus_right : type g m n mn. (m, n, mn) plus -> (g, n) occurs -> (g, mn) occurs =
   fun mn o ->
    match (mn, o) with
    | Zero, _ -> .
    | Suc _, Occurs_now -> Occurs_now
    | Suc (mn, _), Occurs_later o -> Occurs_later (occurs_plus_right mn o)

  let rec occurs_plus_left : type g m n mn. (m, n, mn) plus -> (g, m) occurs -> (g, mn) occurs =
   fun mn o ->
    match mn with
    | Zero -> o
    | Suc (mn, _) -> Occurs_later (occurs_plus_left mn o)

  let rec unoccurs_plus : type g m n mn.
      (m, n, mn) plus -> (g, m) unoccurs -> (g, n) unoccurs -> (g, mn) unoccurs =
   fun mn um un ->
    match (mn, un) with
    | Zero, Unoccurs_emp -> um
    | Suc (mn, _), Unoccurs_suc (un, ap) -> Unoccurs_suc (unoccurs_plus mn um un, ap)
end

module MakeExp (G : PermutableExp) = struct
  include Make (G)

  (* ********** Exponentiation ********** *)

  (* If our generators come with a "number of endpoints" assigned to each of them, then by the "exp" of a word we mean the natural number obtained by multiplying together all those numbers for each generator in it. *)

  type (_, _) exp =
    | Zero : (zero, N.one) exp
    | Suc :
        ('g, 'n) G.endpoints * ('m, 'nm) exp * ('nm, 'n, 'nmn) N.times
        -> (('m, 'g) suc, 'nmn) exp

  type _ has_exp = Has_exp : ('b, 'c) exp -> 'b has_exp

  let rec exp_in : type b c. (b, c) exp -> b t = function
    | Zero -> Word Zero
    | Suc (g, p, _) ->
        let (Word x) = exp_in p in
        Word (Suc (x, G.endpoints_in g))

  let exp_out : type b ab. (b, ab) exp -> ab N.t =
   fun ab ->
    match ab with
    | Zero -> N.one
    | Suc (_, _, aba) -> N.times_out aba

  let rec exp : type b. b t -> b has_exp =
   fun b ->
    match b with
    | Word Zero -> Has_exp Zero
    | Word (Suc (b, g)) ->
        let (Has_exp ab) = exp (Word b) in
        let (Endpoints e) = G.has_endpoints g in
        let (Has_times aba) = N.times (exp_out ab) (G.endpoints_out e) in
        Has_exp (Suc (e, ab, aba))

  let rec exp_uniq : type b ab ab'. (b, ab) exp -> (b, ab') exp -> (ab, ab') Eq.t =
   fun ab ab' ->
    match (ab, ab') with
    | Zero, Zero -> Eq
    | Suc (e, ab, aba), Suc (e', ab', ab'a) ->
        let Eq = exp_uniq ab ab' in
        let Eq = G.endpoints_uniq e e' in
        N.times_uniq aba ab'a

  let rec exp_plus : type b c exp_b exp_c b_plus_c exp__b_plus_c.
      (b, exp_b) exp ->
      (c, exp_c) exp ->
      (b, c, b_plus_c) plus ->
      (b_plus_c, exp__b_plus_c) exp ->
      (exp_b, exp_c, exp__b_plus_c) N.times =
   fun exp_b exp_c b_plus_c exp__b_plus_c ->
    match b_plus_c with
    | Zero ->
        let Zero = exp_c in
        let Eq = exp_uniq exp_b exp__b_plus_c in
        N.times_one (exp_out exp_b)
    | Suc (b_plus_c', _) ->
        let (Suc (e, exp_c', exp_c'__times_a)) = exp_c in
        let (Suc (e', exp__b_plus_c', exp__b_plus_c'___times_a)) = exp__b_plus_c in
        let Eq = G.endpoints_uniq e e' in
        let exp_b__times__exp_c' = exp_plus exp_b exp_c' b_plus_c' exp__b_plus_c' in
        N.times_assocr (exp_out exp_b) exp_b__times__exp_c' exp_c'__times_a exp__b_plus_c'___times_a
end

(* Intrinsically well-typed maps with words as their domains, whose output type is parametrized by the word type and by an additional parameter.  This requires being given a similar kind of map for the type of generators, such as for natural numbers. *)

(* We define the word-maps as a sort of "rose tree" consisting of generator-maps whose entries are word-maps.  Since the output families of the generator-maps are specified with a module parameter, this requires a recursive module.  For some reason it doesn't seem to work to use a destructive substitution here, so we use a type equation and a handicrafted module later so that we can expose a destructive substitution one to the user. *)

module rec Def : functor (G : Comparable) (GM : MAP_MAKER with module Key = G) (F : Fam2) -> sig
  (* We have to use the extra parameter of the generator-maps to determine the rest of the word after that generator, but we also want to carry through an extra parameter on the word-maps (so that in particular the operation can be iterated).  So we use a GADT to pair up the two parameters as their product. *)
  module M : sig
    type (_, _) t = Wrapmap : ('a, ('b, 'n) snoc) Def(G)(GM)(F).map -> ('a * 'b, 'n) t
  end

  module DM : module type of GM.Make (M)

  type ('a, 'b) map = Empty | Entry of ('a, 'b) F.t option * ('a * 'b) DM.t
end =
functor
  (G : Comparable)
  (GM : MAP_MAKER with module Key = G)
  (F : Fam2)
  ->
  struct
    module M = struct
      type (_, _) t = Wrapmap : ('a, ('b, 'n) snoc) Def(G)(GM)(F).map -> ('a * 'b, 'n) t
    end

    module DM = GM.Make (M)

    type ('a, 'b) map = Empty | Entry of ('a, 'b) F.t option * ('a * 'b) DM.t
  end

module Internal (G : Permutable) (GM : MAP_MAKER with module Key = G) (F : Fam2) = struct
  module W = Make (G)
  module Map = Def (G) (GM) (F)

  let rec find_opt : type a b c bc.
      (b, c, bc) W.bplus -> c W.fwd -> (a, b) Map.map -> (a, bc) F.t option =
   fun bc c map ->
    let open Monad.Ops (Monad.Maybe) in
    match map with
    | Empty -> None
    | Entry (x, xs) -> (
        match (bc, c) with
        | Append_nil, _ -> x
        | Append_cons bc, Cons (n, c) ->
            let* (Wrapmap xs) = Map.DM.find_opt n xs in
            find_opt bc c xs)

  let rec add : type a b c bc.
      (b, c, bc) W.bplus -> c W.fwd -> (a, bc) F.t -> (a, b) Map.map -> (a, b) Map.map =
   fun bc c x map ->
    match (bc, c, map) with
    | Append_nil, Nil, Empty -> Entry (Some x, Map.DM.empty)
    | Append_nil, Nil, Entry (_, xs) -> Entry (Some x, xs)
    | Append_cons bc, Cons (n, c), Empty ->
        let e = Map.DM.empty in
        Entry (None, Map.DM.add n (Wrapmap (add bc c x Empty)) e)
    | Append_cons bc, Cons (n, c), Entry (y, xs) ->
        Entry
          ( y,
            Map.DM.update n
              (function
                | Some (Map.M.Wrapmap zs) -> Some (Map.M.Wrapmap (add bc c x zs))
                | None -> Some (Map.M.Wrapmap (add bc c x Empty)))
              xs )

  let rec update : type a b c bc.
      (b, c, bc) W.bplus ->
      c W.fwd ->
      ((a, bc) F.t option -> (a, bc) F.t option) ->
      (a, b) Map.map ->
      (a, b) Map.map =
   fun bc c f map ->
    match (bc, c, map) with
    | Append_nil, Nil, Map.Empty -> Entry (f None, Map.DM.empty)
    | Append_nil, Nil, Entry (x, xs) -> Entry (f x, xs)
    | Append_cons bc, Cons (n, c), Map.Empty ->
        let e = Map.DM.empty in
        Entry (None, Map.DM.add n (Wrapmap (update bc c f Empty)) e)
    | Append_cons bc, Cons (n, c), Entry (y, xs) ->
        Entry
          ( y,
            Map.DM.update n
              (function
                | Some (Map.M.Wrapmap zs) -> Some (Map.M.Wrapmap (update bc c f zs))
                | None -> Some (Map.M.Wrapmap (update bc c f Empty)))
              xs )

  let rec remove : type a b c bc. (b, c, bc) W.bplus -> c W.fwd -> (a, b) Map.map -> (a, b) Map.map
      =
   fun bc c map ->
    match (bc, c, map) with
    | _, _, Empty -> Empty
    | Append_nil, Nil, Entry (_, xs) -> Entry (None, xs)
    | Append_cons bc, Cons (n, c), Entry (y, xs) ->
        Entry
          ( y,
            Map.DM.update n
              (Option.map (fun (Map.M.Wrapmap zs) -> Map.M.Wrapmap (remove bc c zs)))
              xs )

  type 'a mapper = { map : 'g. 'g W.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

  let rec map : type a b. a mapper -> b W.t -> (a, b) Map.map -> (a, b) Map.map =
   fun f b m ->
    match m with
    | Empty -> Empty
    | Entry (x, xs) ->
        Entry
          ( Option.map (f.map b) x,
            Map.DM.map { map = (fun w (Wrapmap x) -> Wrapmap (map f (W.suc b w) x)) } xs )

  type 'a iterator = { it : 'g. 'g W.t -> ('a, 'g) F.t -> unit }

  let rec iter : type a b. a iterator -> b W.t -> (a, b) Map.map -> unit =
   fun f b m ->
    match m with
    | Empty -> ()
    | Entry (x, xs) ->
        Option.iter (f.it b) x;
        Map.DM.iter { it = (fun w (Wrapmap x) -> iter f (W.suc b w) x) } xs
end

module Map (G : Permutable) (GM : MAP_MAKER with module Key := G) :
  MAP_MAKER with module Key := Make(G) = struct
  module Make (F : Fam2) = struct
    module GM2 = struct
      module Key = G
      include GM
    end

    open Internal (G) (GM2) (F)
    module W = W

    let empty = Map.Empty

    let find_opt : type a b. b W.t -> (a, emp) Map.map -> (a, b) F.t option =
     fun b map ->
      let (To_fwd (c, bc)) = W.to_fwd b in
      find_opt bc c map

    let add : type a b. b W.t -> (a, b) F.t -> (a, emp) Map.map -> (a, emp) Map.map =
     fun b x map ->
      let (To_fwd (c, bc)) = W.to_fwd b in
      add bc c x map

    let update : type a b.
        b W.t -> ((a, b) F.t option -> (a, b) F.t option) -> (a, emp) Map.map -> (a, emp) Map.map =
     fun b f map ->
      let (To_fwd (c, bc)) = W.to_fwd b in
      update bc c f map

    let remove : type a b. b W.t -> (a, emp) Map.map -> (a, emp) Map.map =
     fun b map ->
      let (To_fwd (c, bc)) = W.to_fwd b in
      remove bc c map

    type 'a mapper = { map : 'g. 'g W.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

    let map : type a. a mapper -> (a, emp) Map.map -> (a, emp) Map.map =
     fun f m -> map { map = (fun x -> f.map x) } W.zero m

    type 'a iterator = { it : 'g. 'g W.t -> ('a, 'g) F.t -> unit }

    let iter : type a. a iterator -> (a, emp) Map.map -> unit =
     fun f m -> iter { it = (fun w x -> f.it w x) } W.zero m

    type 'a t = ('a, emp) Map.map
  end
end

(* Now we can iterate and build words of words of words! *)
(*
module W = Make (N)
module WMap = Map (N) (Nmap)
module W2 = Make (W)
module WMap2 = Map (W) (WMap)
module W3 = Make (W2)
module WMap3 = Map (W2) (WMap2)
*)

(* Monoid homomorphisms determined by a map on generators *)

module Hom (G : Permutable) (Cod : Monoid) (F : Function with module Dom = G and module Cod = Cod) =
struct
  module Dom = Make (G)
  module Cod = Cod

  type (_, _) t =
    | Zero : (Dom.zero, Cod.zero) t
    | Suc : ('m, 'n1) t * ('g, 'n2) F.t * ('n1, 'n2, 'n3) Cod.plus -> (('m, 'g) Dom.suc, 'n3) t

  let rec dom : type a x. (a, x) t -> a Dom.t = function
    | Zero -> Word Zero
    | Suc (fm, fg, _) -> Dom.suc (dom fm) (F.dom fg)

  let rec cod : type a x. (a, x) t -> x Cod.t = function
    | Zero -> Cod.zero
    | Suc (fm, _, n12) -> Cod.plus_out (cod fm) n12

  type _ exists = Exists : ('a, 'x) t -> 'a exists

  let rec exists : type a. a Dom.t -> a exists = function
    | Word Zero -> Exists Zero
    | Word (Suc (m, g)) ->
        let (Exists fm) = exists (Word m) in
        let (Exists fg) = F.exists g in
        let (Plus n12) = Cod.plus (F.cod fg) in
        Exists (Suc (fm, fg, n12))

  let rec uniq : type a x1 x2. (a, x1) t -> (a, x2) t -> (x1, x2) Eq.t =
   fun f1 f2 ->
    match (f1, f2) with
    | Zero, Zero -> Eq
    | Suc (m1, g1, n1), Suc (m2, g2, n2) ->
        let Eq = uniq m1 m2 in
        let Eq = F.uniq g1 g2 in
        let Eq = Cod.plus_uniq n1 n2 in
        Eq

  let zero : (Dom.zero, Cod.zero) t = Zero

  type (_, _, _) plus = Plus : ('c, 'z) t * ('x, 'y, 'z) Cod.plus -> ('x, 'y, 'c) plus

  let rec plus : type a b c x y. (a, x) t -> (b, y) t -> (a, b, c) Dom.plus -> (x, y, c) plus =
   fun fa fb ab ->
    match (fb, ab) with
    | Zero, Zero -> Plus (fa, Cod.plus_zero (cod fa))
    | Suc (fb, fg, y_fg), Suc (ab, _) ->
        let (Plus (fc, xy)) = plus fa fb ab in
        let (Plus xy_fg) = Cod.plus (F.cod fg) in
        let x_yfg = Cod.plus_assocr xy y_fg xy_fg in
        Plus (Suc (fc, fg, xy_fg), x_yfg)
end

module HomCheck
    (G : Permutable)
    (Cod : Monoid)
    (F : Function with module Dom = G and module Cod = Cod) : Function with module Cod = Cod =
  Hom (G) (Cod) (F)

module HomPerm
    (G : Permutable)
    (Cod : MonoidPerm)
    (F :
      PermFunction
        with module Dom = G
         and module Cod = Cod
         and type ('a, 'b) dom_commute = ('a, 'b) G.commute
         and type ('x, 'y) cod_commute = ('x, 'y) Cod.commute) =
struct
  module H = Hom (G) (Cod) (F)
  module Dom = H.Dom

  type (_, _, _, _) uninsert =
    | Uninsert :
        ('a, 'x) H.t * ('m, 'n) F.t * ('x, 'n, 'xn) Cod.plus * ('xn, 'y) Cod.permute
        -> ('a, 'm, 'b, 'y) uninsert

  let rec uninsert : type a m b y. (a, m, b) Dom.insert -> (b, y) H.t -> (a, m, b, y) uninsert =
   fun i fb ->
    match i with
    | Now ->
        let (Suc (fa, fm, xn)) = fb in
        Uninsert (fa, fm, xn, Cod.perm_id (Cod.plus_out (H.cod fa) xn))
    (* The generator being uninserted moves past the generator k here, so in the codomain their images l and n must be swapped, which is allowed because the homomorphism transports the witness that m and k commute. *)
    | Later (c, i) ->
        let (Suc (fb, fk, yl)) = fb in
        let (Uninsert (fa, fm, xn, perm_xn_y)) = uninsert i fb in
        let x = H.cod fa in
        let l = Cod.plus_right yl in
        let n = Cod.plus_right xn in
        let ln_commute = Cod.commute_inv n l (F.commute fm fk c) in
        let (Plus nl) = Cod.plus l in
        let (Plus ln) = Cod.plus n in
        let (Plus xl) = Cod.plus l in
        let (Plus xn_l) = Cod.plus l in
        let (Plus xl_n) = Cod.plus n in
        let x_ln = Cod.plus_assocr xl ln xl_n in
        let x_nl = Cod.plus_assocr xn nl xn_l in
        let perm_xln_xnl =
          Cod.perm_plus_perm (Cod.perm_id x) x_ln x_nl (Cod.perm_swap ln_commute ln nl) in
        let perm_xnl_yl = Cod.perm_plus_perm perm_xn_y xn_l yl (Cod.perm_id l) in
        let perm_xln_yl = Cod.perm_comp perm_xln_xnl perm_xnl_yl in
        Uninsert (Suc (fa, fk, xl), fm, xl_n, perm_xln_yl)

  (* A permutation grows its codomain by a generator and its domain by an insertion, so we peel a generator off the homomorphism on the codomain and uninsert the one on the domain. *)
  let rec permute : type a x b y.
      (a, x) H.t -> (b, y) H.t -> (a, b) Dom.permute -> (x, y) Cod.permute =
   fun fa fb p ->
    match p with
    | Zero ->
        let Eq = H.uniq fa fb in
        Cod.perm_id (H.cod fa)
    | Suc (p, _, i) ->
        let (Suc (fb, fg, wy)) = fb in
        let (Uninsert (fa, fg', xn, xn_x)) = uninsert i fa in
        let Eq = F.uniq fg' fg in
        let x_w = permute fa fb p in
        Cod.perm_comp (Cod.perm_inv xn_x)
          (Cod.perm_plus_perm x_w xn wy (Cod.perm_id (Cod.plus_right xn)))
end

(* Homomorphisms with forwards-ness *)

module HomFwd
    (G : Permutable)
    (Cod : MonoidFwd)
    (F : Function with module Dom = G and module Cod = Cod) =
struct
  module H = Hom (G) (Cod) (F)

  type (_, _) fwd =
    | Zero : (nil, Cod.fwd_zero) fwd
    | Suc : ('g, 'n1) F.t * ('m, 'n2) fwd * ('n1, 'n2, 'n3) Cod.fplus -> (('g, 'm) cons, 'n3) fwd

  let rec fwd_dom : type a x. (a, x) fwd -> a H.Dom.fwd = function
    | Zero -> Nil
    | Suc (fn, fa, _) -> Cons (F.dom fn, fwd_dom fa)

  type (_, _, _) bplus = Bplus : ('c, 'z) H.t * ('x, 'y, 'z) Cod.bplus -> ('x, 'y, 'c) bplus

  let rec bplus : type a b c x y.
      (a, x) H.t -> (b, y) fwd -> (a, b, c) H.Dom.bplus -> (x, y, c) bplus =
   fun fa fb ab ->
    match (fb, ab) with
    | Zero, Append_nil -> Bplus (fa, Cod.bplus_zero (H.cod fa))
    | Suc (fg, fb, fg_y), Append_cons ab ->
        let (Plus x_fg) = Cod.plus (F.cod fg) in
        let (Bplus (fc, xfg_y)) = bplus (Suc (fa, fg, x_fg)) fb ab in
        let x_fgy = Cod.bfplus_assocr x_fg fg_y xfg_y in
        Bplus (fc, x_fgy)

  include H
end

(* Homomorphisms with permutations AND forwardsness *)

module HomPermFwd
    (G : Permutable)
    (Cod : MonoidPermFwd)
    (F :
      PermFunction
        with module Dom = G
         and module Cod = Cod
         and type ('a, 'b) dom_commute = ('a, 'b) G.commute
         and type ('x, 'y) cod_commute = ('x, 'y) Cod.commute) =
struct
  include HomPerm (G) (Cod) (F)
  include HomFwd (G) (Cod) (F)
end

(* Parametrized homomorphisms *)

module Hom2 (G : Permutable) (Cod : Monoid) (F : Function2 with module Dom = G and module Cod = Cod) =
struct
  module Param = F.Param
  module Dom = Make (G)
  module Cod = Cod

  type (_, _, _) t =
    | Zero : ('param, Dom.zero, Cod.zero) t
    | Suc :
        ('param, 'm, 'n1) t * ('param, 'g, 'n2) F.t * ('n1, 'n2, 'n3) Cod.plus
        -> ('param, ('m, 'g) Dom.suc, 'n3) t

  let zero = Zero
  let suc fa fg xy = Suc (fa, fg, xy)

  let rec dom : type param a x. (param, a, x) t -> a Dom.t = function
    | Zero -> Word Zero
    | Suc (fm, fg, _) -> Dom.suc (dom fm) (F.dom fg)

  let rec cod : type param a x. param Param.t -> (param, a, x) t -> x Cod.t =
   fun p -> function
    | Zero -> Cod.zero
    | Suc (fm, _, n12) -> Cod.plus_out (cod p fm) n12

  type (_, _) exists = Exists : ('param, 'a, 'x) t -> ('param, 'a) exists

  let rec exists : type param a. param Param.t -> a Dom.t -> (param, a) exists =
   fun param -> function
    | Word Zero -> Exists Zero
    | Word (Suc (m, g)) ->
        let (Exists fm) = exists param (Word m) in
        let (Exists fg) = F.exists param g in
        let (Plus n12) = Cod.plus (F.cod param fg) in
        Exists (Suc (fm, fg, n12))

  let rec uniq : type param a x1 x2. (param, a, x1) t -> (param, a, x2) t -> (x1, x2) Eq.t =
   fun f1 f2 ->
    match (f1, f2) with
    | Zero, Zero -> Eq
    | Suc (m1, g1, n1), Suc (m2, g2, n2) ->
        let Eq = uniq m1 m2 in
        let Eq = F.uniq g1 g2 in
        let Eq = Cod.plus_uniq n1 n2 in
        Eq

  type (_, _, _, _) plus =
    | Plus : ('param, 'c, 'z) t * ('x, 'y, 'z) Cod.plus -> ('param, 'x, 'y, 'c) plus

  let rec plus : type param a b c x y.
      param Param.t ->
      (param, a, x) t ->
      (param, b, y) t ->
      (a, b, c) Dom.plus ->
      (param, x, y, c) plus =
   fun param fa fb ab ->
    match (fb, ab) with
    | Zero, Zero -> Plus (fa, Cod.plus_zero (cod param fa))
    | Suc (fb, fg, y_fg), Suc (ab, _) ->
        let (Plus (fc, xy)) = plus param fa fb ab in
        let (Plus xy_fg) = Cod.plus (F.cod param fg) in
        let x_yfg = Cod.plus_assocr xy y_fg xy_fg in
        Plus (Suc (fc, fg, xy_fg), x_yfg)
end

module Hom2Perm
    (G : Permutable)
    (Cod : MonoidPerm)
    (F :
      PermFunction2
        with module Dom = G
         and module Cod = Cod
         and type ('a, 'b) dom_commute = ('a, 'b) G.commute
         and type ('x, 'y) cod_commute = ('x, 'y) Cod.commute) =
struct
  module H = Hom2 (G) (Cod) (F)
  module Param = F.Param
  module Dom = H.Dom

  type (_, _, _, _, _) uninsert =
    | Uninsert :
        ('param, 'a, 'x) H.t * ('param, 'm, 'n) F.t * ('x, 'n, 'xn) Cod.plus * ('xn, 'y) Cod.permute
        -> ('param, 'a, 'm, 'b, 'y) uninsert

  let rec uninsert : type param a m b y.
      param Param.t -> (a, m, b) Dom.insert -> (param, b, y) H.t -> (param, a, m, b, y) uninsert =
   fun param i fb ->
    match i with
    | Now ->
        let (Suc (fa, fm, xn)) = fb in
        Uninsert (fa, fm, xn, Cod.perm_id (Cod.plus_out (H.cod param fa) xn))
    | Later (c, i) ->
        let (Suc (fb, fk, yl)) = fb in
        let (Uninsert (fa, fm, xn, perm_xn_y)) = uninsert param i fb in
        let x = H.cod param fa in
        let l = Cod.plus_right yl in
        let n = Cod.plus_right xn in
        let ln_commute = Cod.commute_inv n l (F.commute param fm fk c) in
        let (Plus nl) = Cod.plus l in
        let (Plus ln) = Cod.plus n in
        let (Plus xl) = Cod.plus l in
        let (Plus xn_l) = Cod.plus l in
        let (Plus xl_n) = Cod.plus n in
        let x_ln = Cod.plus_assocr xl ln xl_n in
        let x_nl = Cod.plus_assocr xn nl xn_l in
        let perm_xln_xnl =
          Cod.perm_plus_perm (Cod.perm_id x) x_ln x_nl (Cod.perm_swap ln_commute ln nl) in
        let perm_xnl_yl = Cod.perm_plus_perm perm_xn_y xn_l yl (Cod.perm_id l) in
        let perm_xln_yl = Cod.perm_comp perm_xln_xnl perm_xnl_yl in
        Uninsert (Suc (fa, fk, xl), fm, xl_n, perm_xln_yl)

  let rec permute : type param a x b y.
      param Param.t ->
      (param, a, x) H.t ->
      (param, b, y) H.t ->
      (a, b) Dom.permute ->
      (x, y) Cod.permute =
   fun param fa fb p ->
    match p with
    | Zero ->
        let Eq = H.uniq fa fb in
        Cod.perm_id (H.cod param fa)
    | Suc (p, _, i) ->
        let (Suc (fb, fg, wy)) = fb in
        let (Uninsert (fa, fg', xn, xn_x)) = uninsert param i fa in
        let Eq = F.uniq fg' fg in
        let x_w = permute param fa fb p in
        Cod.perm_comp (Cod.perm_inv xn_x)
          (Cod.perm_plus_perm x_w xn wy (Cod.perm_id (Cod.plus_right xn)))
end

(* (Parametrized) functoriality is the homomorphism induced by a function composed with the monad unit. *)

module Fmap
    (Dom : Permutable)
    (Cod : Permutable)
    (F :
      PermFunction2
        with module Dom = Dom
         and module Cod = Cod
         and type ('a, 'b) dom_commute = ('a, 'b) Dom.commute
         and type ('x, 'y) cod_commute = ('x, 'y) Cod.commute) =
struct
  module CodMonoid = Make (Cod)
  module C = Cod

  module FMonoid = struct
    module Param = F.Param
    module Dom = Dom
    module Cod = CodMonoid

    type (_, _, _) t = Inject : ('p, 'a, 'b) F.t -> ('p, 'a, (Cod.zero, 'b) Cod.suc) t

    let dom : type p a b. (p, a, b) t -> a Dom.t = fun (Inject x) -> F.dom x

    let cod : type p a b. p Param.t -> (p, a, b) t -> b Cod.t =
     fun p (Inject x) -> Cod.suc Cod.zero (F.cod p x)

    type (_, _) exists = Exists : ('p, 'a, 'b) t -> ('p, 'a) exists

    let exists : type p a. p Param.t -> a Dom.t -> (p, a) exists =
     fun p x ->
      let (Exists fx) = F.exists p x in
      Exists (Inject fx)

    let uniq : type p a b1 b2. (p, a, b1) t -> (p, a, b2) t -> (b1, b2) Eq.t =
     fun f1 f2 ->
      match (f1, f2) with
      | Inject f1, Inject f2 ->
          let Eq = F.uniq f1 f2 in
          Eq
  end

  include Hom2 (Dom) (CodMonoid) (FMonoid)

  let suc p fa fg = Suc (fa, Inject fg, Suc (Zero, F.cod p fg))

  (* In this case, we have insertions in the codomain too, so we can be more precise about how the homomorphism acts on them. *)

  type (_, _, _, _) uninsert =
    | Uninsert :
        ('p, 'x, 'fx) F.t * ('zs, 'fx, 'ws) CodMonoid.insert * ('p, 'xs, 'zs) t
        -> ('p, 'x, 'xs, 'ws) uninsert

  let rec uninsert : type p xs x ys ws.
      p Param.t -> (xs, x, ys) Dom.insert -> (p, ys, ws) t -> (p, x, xs, ws) uninsert =
   fun p i fxs ->
    match (fxs, i) with
    | Suc (fxs, Inject fx, Suc (Zero, _)), Now -> Uninsert (fx, Now, fxs)
    (* The removed generator moves past this one, and the homomorphism transports that commutation to their images. *)
    | Suc (fxs, Inject fk, Suc (Zero, yy)), Later (c, i) ->
        let (Uninsert (u, fi, fxs)) = uninsert p i fxs in
        Uninsert (u, Later (F.commute p u fk c, fi), Suc (fxs, Inject fk, Suc (Zero, yy)))
    | Zero, _ -> .

  type (_, _, _, _) uncoinsert =
    | Uncoinsert :
        ('p, 'x, 'z) F.t * ('xs, 'x, 'ys) Dom.insert * ('p, 'xs, 'zs) t
        -> ('p, 'z, 'ys, 'zs) uncoinsert

  let rec uncoinsert : type p ys z zs ws.
      (zs, z, ws) CodMonoid.insert -> (p, ys, ws) t -> (p, z, ys, zs) uncoinsert =
   fun i fxs ->
    match i with
    | Now ->
        let (Suc (fxs, Inject fx, Suc (Zero, _))) = fxs in
        Uncoinsert (fx, Now, fxs)
    (* Dually to uninsert, we have to reflect the commutation of the images back to their preimages. *)
    | Later (c, i) ->
        let (Suc (fxs, Inject fk, Suc (Zero, yy))) = fxs in
        let (Uncoinsert (fx', fi, fxs)) = uncoinsert i fxs in
        Uncoinsert (fx', Later (F.uncommute fx' fk c, fi), Suc (fxs, Inject fk, Suc (Zero, yy)))
end
