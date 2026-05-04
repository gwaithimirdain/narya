open Signatures
open Tlist
open Tbwd
open Monoid

(* Type-level free monoids.  The type of generators is specified by a type family in a module parameter.  If there is exactly one generator, the result should be isomorphic to the type-level (backwards) natural numbers. *)

module Make (G : Comparable) = struct
  (* As the words themselves, we use type-level backwards lists (Tbwd) of generators.  TODO: Do we ever really use Tbwds, or should we just use Words?  *)
  type zero = emp
  type ('n, 'g) suc = ('n, 'g) snoc

  (* ********** Addition ********** *)

  (* Addition is appending two Tbwds.  Note that this is different from Tbwd.append, which appends a *forwards* list on the right of a backwards one.  It also ensures that the appended list consists of valid generators. *)

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

  (* We postpone suc_plus_eq_suc until after we have insertions, to characterize its output value more correctly. *)

  type (_, _, _, _) suc_plus =
    | Suc_plus :
        (('m, 'h) suc, 'q, 'p) plus * ((zero, 'h) suc, 'q, ('n, 'g) suc) plus
        -> ('m, 'n, 'g, 'p) suc_plus

  let rec suc_plus : type m n g p. (m, (n, g) suc, p) plus -> (m, n, g, p) suc_plus = function
    | Suc (Zero, _) -> Suc_plus (Zero, Zero)
    | Suc ((Suc _ as mn), g) ->
        let (Suc_plus (mq, kq)) = suc_plus mn in
        Suc_plus (Suc (mq, g), Suc (kq, g))

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

  (* ********** Well-scoped De Bruijn indices ********** *)

  (* The analogue of these for words is just Tbwd.insert. *)

  type (_, _, _, _) plus_insert =
    | Plus_insert : ('m, 'p, 'mp) plus * ('mp, 'g, 'mn) Tbwd.insert -> ('m, 'p, 'mn, 'g) plus_insert

  let rec plus_insert : type m n mn p g.
      (m, n, mn) plus -> (p, g, n) Tbwd.insert -> (m, p, mn, g) plus_insert =
   fun mn i ->
    match i with
    | Now ->
        let (Suc (mn, _)) = mn in
        Plus_insert (mn, Now)
    | Later i ->
        let (Suc (mn, g)) = mn in
        let (Plus_insert (mp, j)) = plus_insert mn i in
        Plus_insert (Suc (mp, g), Later j)

  type (_, _, _, _) insert_plus =
    | Insert_plus : ('p, 'n, 'pn) plus * ('pn, 'g, 'mn) Tbwd.insert -> ('p, 'n, 'mn, 'g) insert_plus

  let rec insert_plus : type m n mn g p.
      (p, g, m) Tbwd.insert -> (m, n, mn) plus -> (p, n, mn, g) insert_plus =
   fun i mn ->
    match mn with
    | Zero -> Insert_plus (Zero, i)
    | Suc (mn, g) ->
        let (Insert_plus (pn, j)) = insert_plus i mn in
        Insert_plus (Suc (pn, g), Later j)

  type (_, _, _, _) swap_inserts =
    | Swap_indices :
        ('q, 'l, 'm) Tbwd.insert * ('p, 'k, 'q) Tbwd.insert
        -> ('m, 'k, 'l, 'p) swap_inserts

  let rec swap_inserts : type m n p k l.
      (n, k, m) Tbwd.insert -> (p, l, n) Tbwd.insert -> (m, k, l, p) swap_inserts =
   fun k l ->
    match k with
    | Now -> (
        match l with
        | Now -> Swap_indices (Later l, Now)
        | Later _ -> Swap_indices (Later l, Now))
    | Later k' -> (
        match l with
        | Now -> Swap_indices (Now, k')
        | Later l' ->
            let (Swap_indices (l'', k'')) = swap_inserts k' l' in
            Swap_indices (Later l'', Later k''))

  let rec insert_equiv : type m n g p q.
      (p, g, m) Tbwd.insert -> (q, g, n) Tbwd.insert -> unit option =
   fun k l ->
    match (k, l) with
    | Now, Now -> Some ()
    | Later k, Later l -> insert_equiv k l
    | _, _ -> None

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

  (* Now we can define suc_plus_eq_suc in a way that correctly records the relationship between 'q and 'p.  *)
  type (_, _, _, _) suc_plus_eq_suc =
    | Suc_plus_eq_suc :
        (('m, 'g) suc, 'n, 'q) plus * ('p, 'g, 'q) Tbwd.insert
        -> ('m, 'g, 'n, 'p) suc_plus_eq_suc

  let rec suc_plus_eq_suc : type m g n p. (m, n, p) plus -> (m, g, n, p) suc_plus_eq_suc = function
    | Zero -> Suc_plus_eq_suc (Zero, Now)
    | Suc (x, g) ->
        let (Suc_plus_eq_suc (y, i)) = suc_plus_eq_suc x in
        Suc_plus_eq_suc (Suc (y, g), Later i)

  (* ********** More about insertion ********** *)

  let rec insert : type a n b. (a, n, b) Tbwd.insert -> a t -> n G.t -> b t =
   fun i (Word a) n ->
    match i with
    | Now -> Word (Suc (a, n))
    | Later i ->
        let (Suc (a, k)) = a in
        let (Word ins) = insert i (Word a) n in
        Word (Suc (ins, k))

  let rec uninsert : type a n b. (a, n, b) Tbwd.insert -> b t -> a t =
   fun i b ->
    match i with
    | Now ->
        let (Word (Suc (b, _))) = b in
        Word b
    | Later i ->
        let (Word (Suc (b, n))) = b in
        let (Word ins) = uninsert i (Word b) in
        Word (Suc (ins, n))

  let rec inserted : type a n b. (a, n, b) Tbwd.insert -> b t -> n G.t =
   fun i b ->
    match i with
    | Now ->
        let (Word (Suc (_, n))) = b in
        n
    | Later i ->
        let (Word (Suc (b, _))) = b in
        inserted i (Word b)

  (* ********** Permutations ********** *)

  (* A free monoids is not commutative, but it is the object set of a free symmetric strict monoidal category.  Here are the morphisms in that category.  *)

  type ('a, 'b) permute = ('a, 'b) Tbwd.permute

  (* TODO: The operations in Tbwd are not systematically named.  *)

  let perm_id : type a. a t -> (a, a) permute = fun _ -> Tbwd.id_perm

  let rec perm_dom : type a b. (a, b) permute -> b t -> a t =
   fun p b ->
    match p with
    | Id -> b
    | Insert (p, i) ->
        let (Word permuted) = perm_dom p (uninsert i b) in
        Word (Suc (permuted, inserted i b))

  let perm_comp = Tbwd.comp_permute
  let perm_inv = Tbwd.permute_inv

  let rec insert_of_plus : type b a ba bga g.
      (b, a, ba) plus -> ((b, g) suc, a, bga) plus -> (ba, g, bga) Tbwd.insert =
   fun ba bga ->
    match (ba, bga) with
    | Zero, Zero -> Now
    | Suc (ba, _), Suc (bga, _) -> Later (insert_of_plus ba bga)

  let rec perm_swap : type a b ab ba. (a, b, ab) plus -> (b, a, ba) plus -> (ab, ba) permute =
   fun ab ba ->
    match ab with
    | Zero ->
        let a = plus_right ba in
        let Eq = plus_uniq ba (zero_plus a) in
        perm_id a
    | Suc (ab', _) ->
        let (Plus b'a) = plus (plus_right ba) in
        Insert (perm_swap ab' b'a, insert_of_plus b'a ba)

  let rec perm_plus_perm : type a b ab c d cd.
      (a, c) permute -> (a, b, ab) plus -> (c, d, cd) plus -> (b, d) permute -> (ab, cd) permute =
   fun p ab cd q ->
    match (ab, q) with
    | Zero, Id ->
        let Zero = cd in
        p
    | Suc _, Id -> perm_plus_perm p ab cd (Insert (Id, Now))
    | Suc (ab, _), Insert (q, i) ->
        let (Plus_insert (cd, i)) = plus_insert cd i in
        Insert (perm_plus_perm p ab cd q, i)

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

  type ('a, 'b, 'ab) bplus = ('a, 'b, 'ab) Tbwd.append
  type (_, _) has_bplus = Bplus : ('a, 'b, 'ab) bplus -> ('a, 'b) has_bplus

  let rec bplus : type a b. b fwd -> (a, b) has_bplus = function
    | Nil -> Bplus Append_nil
    | Cons (_, b) ->
        let (Bplus ab) = bplus b in
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

  let rec of_snocs : type a b n ab. a t -> n G.t -> (a, b, n, ab) Tbwd.snocs -> ab t =
   fun a n ab ->
    match ab with
    | Zero -> a
    | Suc ab -> of_snocs (suc a n) n ab

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

  let pos : type a. a pos -> a t = fun (Pos (Word a, g)) -> Word (Suc (a, g))

  type _ compare_zero = Zero : zero compare_zero | Pos : 'n pos -> 'n compare_zero

  let compare_zero : type a. a t -> a compare_zero = function
    | Word Zero -> Zero
    | Word (Suc (a, g)) -> Pos (Pos (Word a, g))
end

module MakeCheck (G : Comparable) : Monoid = Make (G)
module MakeCheckPos (G : Comparable) : MonoidPos = Make (G)
module MakeCheckPerm (G : Comparable) : MonoidPerm = Make (G)

module type ComparableExp = sig
  include Comparable

  type ('g, 'n) endpoints
  type _ has_endpoints = Endpoints : ('g, 'n) endpoints -> 'g has_endpoints

  val endpoints_in : ('g, 'n) endpoints -> 'g t
  val endpoints_out : ('g, 'n) endpoints -> 'n N.t
  val has_endpoints : 'g t -> 'g has_endpoints
  val endpoints_uniq : ('g, 'n1) endpoints -> ('g, 'n2) endpoints -> ('n1, 'n2) Eq.t
end

module MakeExp (G : ComparableExp) = struct
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

module Internal (G : Comparable) (GM : MAP_MAKER with module Key = G) (F : Fam2) = struct
  module W = Make (G)
  module Map = Def (G) (GM) (F)

  let rec find_opt : type a b c bc.
      (b, c, bc) Tbwd.append -> c W.fwd -> (a, b) Map.map -> (a, bc) F.t option =
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
      (b, c, bc) Tbwd.append -> c W.fwd -> (a, bc) F.t -> (a, b) Map.map -> (a, b) Map.map =
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
      (b, c, bc) Tbwd.append ->
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

  let rec remove : type a b c bc.
      (b, c, bc) Tbwd.append -> c W.fwd -> (a, b) Map.map -> (a, b) Map.map =
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

module Map (G : Comparable) (GM : MAP_MAKER with module Key := G) :
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

module Hom (G : Comparable) (Cod : Monoid) (F : Function with module Dom = G and module Cod = Cod) =
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
    (G : Comparable)
    (Cod : Monoid)
    (F : Function with module Dom = G and module Cod = Cod) : Function with module Cod = Cod =
  Hom (G) (Cod) (F)

module HomPerm
    (G : Comparable)
    (Cod : MonoidPerm)
    (F : Function with module Dom = G and module Cod = Cod) =
struct
  module H = Hom (G) (Cod) (F)
  module Dom = H.Dom

  type (_, _, _, _) uninsert =
    | Uninsert :
        ('a, 'x) H.t * ('m, 'n) F.t * ('x, 'n, 'xn) Cod.plus * ('xn, 'y) Cod.permute
        -> ('a, 'm, 'b, 'y) uninsert

  let rec uninsert : type a m b y. (a, m, b) Tbwd.insert -> (b, y) H.t -> (a, m, b, y) uninsert =
   fun i fb ->
    match i with
    | Now ->
        let (Suc (fa, fm, xn)) = fb in
        Uninsert (fa, fm, xn, Cod.perm_id (Cod.plus_out (H.cod fa) xn))
    | Later i ->
        let (Suc (fb, fk, yl)) = fb in
        let (Uninsert (fa, fm, xn, perm_xn_y)) = uninsert i fb in
        let x = H.cod fa in
        let l = Cod.plus_right yl in
        let n = Cod.plus_right xn in
        let (Plus nl) = Cod.plus l in
        let (Plus ln) = Cod.plus n in
        let (Plus xl) = Cod.plus l in
        let (Plus xn_l) = Cod.plus l in
        let (Plus xl_n) = Cod.plus n in
        let x_ln = Cod.plus_assocr xl ln xl_n in
        let x_nl = Cod.plus_assocr xn nl xn_l in
        let perm_xln_xnl = Cod.perm_plus_perm (Cod.perm_id x) x_ln x_nl (Cod.perm_swap ln nl) in
        let perm_xnl_yl = Cod.perm_plus_perm perm_xn_y xn_l yl (Cod.perm_id l) in
        let perm_xln_yl = Cod.perm_comp perm_xln_xnl perm_xnl_yl in
        Uninsert (Suc (fa, fk, xl), fm, xl_n, perm_xln_yl)

  let rec permute : type a x b y.
      (a, x) H.t -> (b, y) H.t -> (a, b) Dom.permute -> (x, y) Cod.permute =
   fun fa fb p ->
    match p with
    | Id ->
        let Eq = H.uniq fa fb in
        Cod.perm_id (H.cod fa)
    | Insert (p, i) ->
        let (Suc (fa, fg, xy)) = fa in
        let (Uninsert (fb, fg', wy, wy_z)) = uninsert i fb in
        let Eq = F.uniq fg fg' in
        let x_w = permute fa fb p in
        Cod.perm_comp (Cod.perm_plus_perm x_w xy wy (Cod.perm_id (Cod.plus_right xy))) wy_z
end

(* Homomorphisms with forwards-ness *)

module HomFwd
    (G : Comparable)
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
    (G : Comparable)
    (Cod : MonoidPermFwd)
    (F : Function with module Dom = G and module Cod = Cod) =
struct
  include HomPerm (G) (Cod) (F)
  include HomFwd (G) (Cod) (F)
end

(* Parametrized homomorphisms *)

module Hom2 (G : Comparable) (Cod : Monoid) (F : Function2 with module Dom = G and module Cod = Cod) =
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
    (G : Comparable)
    (Cod : MonoidPerm)
    (F : Function2 with module Dom = G and module Cod = Cod) =
struct
  module H = Hom2 (G) (Cod) (F)
  module Param = F.Param
  module Dom = H.Dom

  type (_, _, _, _, _) uninsert =
    | Uninsert :
        ('param, 'a, 'x) H.t * ('param, 'm, 'n) F.t * ('x, 'n, 'xn) Cod.plus * ('xn, 'y) Cod.permute
        -> ('param, 'a, 'm, 'b, 'y) uninsert

  let rec uninsert : type param a m b y.
      param Param.t -> (a, m, b) Tbwd.insert -> (param, b, y) H.t -> (param, a, m, b, y) uninsert =
   fun param i fb ->
    match i with
    | Now ->
        let (Suc (fa, fm, xn)) = fb in
        Uninsert (fa, fm, xn, Cod.perm_id (Cod.plus_out (H.cod param fa) xn))
    | Later i ->
        let (Suc (fb, fk, yl)) = fb in
        let (Uninsert (fa, fm, xn, perm_xn_y)) = uninsert param i fb in
        let x = H.cod param fa in
        let l = Cod.plus_right yl in
        let n = Cod.plus_right xn in
        let (Plus nl) = Cod.plus l in
        let (Plus ln) = Cod.plus n in
        let (Plus xl) = Cod.plus l in
        let (Plus xn_l) = Cod.plus l in
        let (Plus xl_n) = Cod.plus n in
        let x_ln = Cod.plus_assocr xl ln xl_n in
        let x_nl = Cod.plus_assocr xn nl xn_l in
        let perm_xln_xnl = Cod.perm_plus_perm (Cod.perm_id x) x_ln x_nl (Cod.perm_swap ln nl) in
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
    | Id ->
        let Eq = H.uniq fa fb in
        Cod.perm_id (H.cod param fa)
    | Insert (p, i) ->
        let (Suc (fa, fg, xy)) = fa in
        let (Uninsert (fb, fg', wy, wy_z)) = uninsert param i fb in
        let Eq = F.uniq fg fg' in
        let x_w = permute param fa fb p in
        Cod.perm_comp (Cod.perm_plus_perm x_w xy wy (Cod.perm_id (Cod.plus_right xy))) wy_z
end

(* (Parametrized) functoriality is the homomorphism induced by a function composed with the monad unit. *)

module Fmap
    (Dom : Comparable)
    (Cod : Comparable)
    (F : Function2 with module Dom = Dom and module Cod = Cod) =
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
        ('p, 'x, 'fx) F.t * ('zs, 'fx, 'ws) Tbwd.insert * ('p, 'xs, 'zs) t
        -> ('p, 'x, 'xs, 'ws) uninsert

  let rec uninsert : type p xs x ys ws.
      (xs, x, ys) Tbwd.insert -> (p, ys, ws) t -> (p, x, xs, ws) uninsert =
   fun i fxs ->
    match (fxs, i) with
    | Suc (fxs, Inject fx, Suc (Zero, _)), Now -> Uninsert (fx, Now, fxs)
    | Suc (fxs, fx, Suc (Zero, yy)), Later i ->
        let (Uninsert (u, fi, fxs)) = uninsert i fxs in
        Uninsert (u, Later fi, Suc (fxs, fx, Suc (Zero, yy)))
    | Zero, _ -> .

  type (_, _, _, _) uncoinsert =
    | Uncoinsert :
        ('p, 'x, 'z) F.t * ('xs, 'x, 'ys) Tbwd.insert * ('p, 'xs, 'zs) t
        -> ('p, 'z, 'ys, 'zs) uncoinsert

  let rec uncoinsert : type p ys z zs ws.
      (zs, z, ws) Tbwd.insert -> (p, ys, ws) t -> (p, z, ys, zs) uncoinsert =
   fun i fxs ->
    match i with
    | Now ->
        let (Suc (fxs, Inject fx, Suc (Zero, _))) = fxs in
        Uncoinsert (fx, Now, fxs)
    | Later i ->
        let (Suc (fxs, fx, Suc (Zero, yy))) = fxs in
        let (Uncoinsert (fx', fi, fxs)) = uncoinsert i fxs in
        Uncoinsert (fx', Later fi, Suc (fxs, fx, Suc (Zero, yy)))
end
