open Util

(* ********** Strict degeneracies ********** *)

(* A strict degeneracy is a degeneracy that doesn't reorder the generators of its codomain.  Thus, walking the domain from the inner end outwards, each generator either survives to the codomain (Suc) or is degenerated away (Degen).  Just as an arbitrary face is a permutation followed by a strict face, an arbitrary degeneracy (see Deg) is a strict degeneracy followed by a permutation. *)

type (_, _) sdeg =
  | Zero : (D.zero, D.zero) sdeg
  | Suc : ('a, 'b) sdeg * 'g D.G.t -> (('a, 'g) D.suc, ('b, 'g) D.suc) sdeg
  | Degen : ('a, 'b) sdeg * 'g D.G.t -> (('a, 'g) D.suc, 'b) sdeg

let rec dom_sdeg : type m n. (m, n) sdeg -> m D.t = function
  | Zero -> D.zero
  | Suc (s, g) -> D.suc (dom_sdeg s) g
  | Degen (s, g) -> D.suc (dom_sdeg s) g

let rec cod_sdeg : type m n. (m, n) sdeg -> n D.t = function
  | Zero -> D.zero
  | Suc (s, g) -> D.suc (cod_sdeg s) g
  | Degen (s, _) -> cod_sdeg s

let rec id_sdeg : type n. n D.t -> (n, n) sdeg = function
  | Word Zero -> Zero
  | Word (Suc (n, g)) -> Suc (id_sdeg (Word n), g)

(* Every dimension is a strict degeneracy of zero. *)
let rec sdeg_zero : type a. a D.t -> (a, D.zero) sdeg = function
  | Word Zero -> Zero
  | Word (Suc (a, g)) -> Degen (sdeg_zero (Word a), g)

let rec is_id_sdeg : type m n. (m, n) sdeg -> (m, n) Eq.t option = function
  | Zero -> Some Eq
  | Degen _ -> None
  | Suc (s, _) -> (
      match is_id_sdeg s with
      | Some Eq -> Some Eq
      | None -> None)

(* Since strict degeneracies preserve order, they compose without any interchange. *)
let rec comp_sdeg : type a b c. (b, c) sdeg -> (a, b) sdeg -> (a, c) sdeg =
 fun s t ->
  match t with
  | Zero ->
      let Zero = s in
      Zero
  | Degen (t, g) -> Degen (comp_sdeg s t, g)
  | Suc (t, g) -> (
      match s with
      | Suc (s, _) -> Suc (comp_sdeg s t, g)
      | Degen (s, _) -> Degen (comp_sdeg s t, g))

(* A strict degeneracy of a positive dimension has positive domain. *)
let sdeg_pos : type m n. n D.pos -> (m, n) sdeg -> m D.pos =
 fun n s ->
  match (n, s) with
  | Pos _, Suc (s, g) -> Pos (dom_sdeg s, g)
  | Pos _, Degen (s, g) -> Pos (dom_sdeg s, g)

(* ********** Inserting into the domain ********** *)

(* Insert a degenerate generator anywhere in the domain, leaving the codomain unchanged. *)
let rec sdeg_insert_degen : type a b g asuc.
    (a, b) sdeg -> g D.G.t -> (a, g, asuc) D.insert -> (asuc, b) sdeg =
 fun s g i ->
  match i with
  | Now -> Degen (s, g)
  | Later i -> (
      match s with
      | Suc (s, h) -> Suc (sdeg_insert_degen s g i, h)
      | Degen (s, h) -> Degen (sdeg_insert_degen s g i, h))

(* Insert a surviving generator anywhere in the domain.  The codomain then acquires it too, in the corresponding place, which we report as an insertion. *)
type (_, _, _) sdeg_insert =
  | Sdeg_insert : ('asuc, 'bsuc) sdeg * ('b, 'g, 'bsuc) D.insert -> ('asuc, 'g, 'b) sdeg_insert

let rec sdeg_insert : type a b g asuc.
    (a, b) sdeg -> g D.G.t -> (a, g, asuc) D.insert -> (asuc, g, b) sdeg_insert =
 fun s g i ->
  match i with
  | Now -> Sdeg_insert (Suc (s, g), Now)
  | Later i -> (
      match s with
      | Suc (s, h) ->
          let (Sdeg_insert (s, j)) = sdeg_insert s g i in
          Sdeg_insert (Suc (s, h), Later j)
      | Degen (s, h) ->
          let (Sdeg_insert (s, j)) = sdeg_insert s g i in
          Sdeg_insert (Degen (s, h), j))

(* Conversely, remove a generator of the codomain along with the generator of the domain that survives to it, reporting the latter as an insertion. *)
type (_, _, _) sdeg_uninsert =
  | Sdeg_uninsert : ('a, 'b) sdeg * ('a, 'g, 'asuc) D.insert -> ('asuc, 'g, 'b) sdeg_uninsert

let rec sdeg_uninsert : type a b g bsuc.
    (a, bsuc) sdeg -> (b, g, bsuc) D.insert -> (a, g, b) sdeg_uninsert =
 fun s i ->
  match (i, s) with
  | Now, Suc (s, _) -> Sdeg_uninsert (s, Now)
  | Later i, Suc (s, h) ->
      let (Sdeg_uninsert (s, j)) = sdeg_uninsert s i in
      Sdeg_uninsert (Suc (s, h), Later j)
  | _, Degen (s, h) ->
      let (Sdeg_uninsert (s, j)) = sdeg_uninsert s i in
      Sdeg_uninsert (Degen (s, h), Later j)

(* Like sdeg_uninsert, but reporting only the numerical position in the domain of the generator that survives to the removed one, rather than an insertion of it.  Since nothing is moved anywhere, this needs no commutation; but for the same reason there is nothing to relate the smaller domain to the original one, so it is existential. *)
type _ sdeg_uninsert_index = Sdeg_uninsert_index : ('a, 'b) sdeg * int -> 'b sdeg_uninsert_index

let rec sdeg_uninsert_index : type a b g bsuc.
    (a, bsuc) sdeg -> (b, g, bsuc) D.insert -> b sdeg_uninsert_index =
 fun s i ->
  match (i, s) with
  | Now, Suc (s, _) -> Sdeg_uninsert_index (s, 0)
  | Later i, Suc (s, h) ->
      let (Sdeg_uninsert_index (s, n)) = sdeg_uninsert_index s i in
      Sdeg_uninsert_index (Suc (s, h), n + 1)
  | _, Degen (s, h) ->
      let (Sdeg_uninsert_index (s, n)) = sdeg_uninsert_index s i in
      Sdeg_uninsert_index (Degen (s, h), n + 1)

(* Dually to sdeg_uninsert, given a generator of the domain, say whether it survives to the codomain, and if so remove both it and its image. *)
type (_, _, _) sdeg_coresidual =
  | Coresidual_degen : ('mpred, 'n) sdeg -> ('mpred, 'g, 'n) sdeg_coresidual
  | Coresidual_keep :
      ('mpred, 'npred) sdeg * ('npred, 'g, 'n) D.insert
      -> ('mpred, 'g, 'n) sdeg_coresidual

let rec sdeg_coresidual : type mpred g m n.
    (m, n) sdeg -> (mpred, g, m) D.insert -> (mpred, g, n) sdeg_coresidual =
 fun s k ->
  match (k, s) with
  | Now, Suc (s, _) -> Coresidual_keep (s, Now)
  | Now, Degen (s, _) -> Coresidual_degen s
  | Later k, Suc (s, h) -> (
      match sdeg_coresidual s k with
      | Coresidual_degen s -> Coresidual_degen (Suc (s, h))
      | Coresidual_keep (s, i) -> Coresidual_keep (Suc (s, h), Later i))
  | Later k, Degen (s, h) -> (
      match sdeg_coresidual s k with
      | Coresidual_degen s -> Coresidual_degen (Degen (s, h))
      | Coresidual_keep (s, i) -> Coresidual_keep (Degen (s, h), i))

(* ********** Sums ********** *)

(* Extend a strict degeneracy by the identity on the right. *)
let rec sdeg_plus : type m n k mk nk.
    (m, n) sdeg -> (n, k, nk) D.plus -> (m, k, mk) D.plus -> (mk, nk) sdeg =
 fun s nk mk ->
  match (nk, mk) with
  | Zero, Zero -> s
  | Suc (nk, g), Suc (mk, _) -> Suc (sdeg_plus s nk mk, g)

(* Extend the domain of a strict degeneracy by a number of degenerate points, leaving the codomain fixed. *)
let rec sdeg_plus_dom : type m n k mk. (m, n) sdeg -> (m, k, mk) D.plus -> (mk, n) sdeg =
 fun s mk ->
  match mk with
  | Zero -> s
  | Suc (mk, g) -> Degen (sdeg_plus_dom s mk, g)

(* Add together two strict degeneracies. *)
let rec sdeg_plus_sdeg : type m n mn k l kl.
    (k, m) sdeg -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) sdeg -> (kl, mn) sdeg =
 fun skm mn kl sln ->
  match sln with
  | Zero ->
      let Zero, Zero = (mn, kl) in
      skm
  | Suc (sln, g) ->
      let Suc (mn, _), Suc (kl, _) = (mn, kl) in
      Suc (sdeg_plus_sdeg skm mn kl sln, g)
  | Degen (sln, g) ->
      let (Suc (kl, _)) = kl in
      Degen (sdeg_plus_sdeg skm mn kl sln, g)

(* ********** Degenerated dimensions ********** *)

(* The word of dimensions degenerated by a strict degeneracy, in domain order. *)
let rec sdeg_degenerated : type m n. (m, n) sdeg -> D.wrapped = function
  | Zero -> Wrap D.zero
  | Suc (s, _) -> sdeg_degenerated s
  | Degen (s, g) ->
      let (Wrap w) = sdeg_degenerated s in
      Wrap (D.suc w g)

(* Whether a strict degeneracy degenerates anything at all. *)
let rec sdeg_is_degenerating : type m n. (m, n) sdeg -> bool = function
  | Zero -> false
  | Suc (s, _) -> sdeg_is_degenerating s
  | Degen _ -> true
