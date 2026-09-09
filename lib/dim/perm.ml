(* ********** Permutations ********** *)

(* A permutation of dimensions is nothing but a permutation of the underlying dimension words, whose definition in Word deliberately matches the definition of degeneracies above.  So the general theory of permutations is inherited from Word, and what remains here is their relationship with degeneracies. *)

type ('m, 'n) perm = ('m, 'n) D.permute =
  | Zero : (D.zero, D.zero) perm
  | Suc : ('a, 'b) perm * 'g D.G.t * ('a, 'g, 'c) D.insert -> ('c, ('b, 'g) D.suc) perm

let dom_perm = D.perm_dom
let cod_perm = D.perm_cod
let id_perm = D.perm_id
let is_id_perm = D.perm_is_id
let perm_inv = D.perm_inv

(* Word composes permutations in diagrammatic order, but here, as for degeneracies, we prefer applicative order. *)
let comp_perm : type a b c. (b, c) perm -> (a, b) perm -> (a, c) perm = fun a b -> D.perm_comp b a

(* Extend a permutation by the identity on an additional dimension. *)
let perm_plus = D.perm_plus

(* Two permutations side by side.  Word takes the two sums in the other order. *)
let perm_plus_perm : type m n mn k l kl.
    (k, m) perm -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) perm -> (kl, mn) perm =
 fun skm mn kl sln -> D.perm_plus_perm skm kl mn sln

(* Add a dimension to the domain of a permutation, inserting it anywhere in the codomain. *)
let perm_with_extra = D.coinsert

(* Two dimensions can be swapped past each other. *)
let perm_swap = D.perm_swap

(* A permutation of a positive dimension has positive domain. *)
let perm_pos = D.perm_pos

(* A permutation with specified domain only *)
type _ perm_to = Perm_to : ('a, 'b) perm -> 'a perm_to
