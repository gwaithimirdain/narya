open Deg

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

(* Every permutation is a degeneracy. *)
let rec deg_of_perm : type m n. (m, n) perm -> (m, n) deg = function
  | Zero -> Zero D.zero
  | Suc (p, g, i) -> Suc (deg_of_perm p, g, i)

(* Conversely, a degeneracy *might* be a permutation. *)
let rec perm_of_deg : type m n. (m, n) deg -> (m, n) perm option = function
  | Zero (Word Zero) -> Some Zero
  | Zero _ -> None
  | Suc (p, g, i) -> (
      match perm_of_deg p with
      | Some p -> Some (Suc (p, g, i))
      | None -> None)

(* A degeneracy with codomain a sum of dimensions might decompose as a sum of a degeneracy and a permutation. *)
type (_, _, _) deg_perm_of_plus =
  | Deg_perm_of_plus :
      ('m, 'l, 'ml) D.plus * ('m, 'n) deg * ('l, 'k) perm
      -> ('ml, 'n, 'k) deg_perm_of_plus
  | None_deg_perm_of_plus : ('mk, 'n, 'k) deg_perm_of_plus

let rec deg_perm_of_plus : type ml n k nk.
    (n, k, nk) D.plus -> (ml, nk) deg -> (ml, n, k) deg_perm_of_plus =
 fun nk s ->
  match nk with
  | Zero -> Deg_perm_of_plus (Zero, s, id_perm D.zero)
  | Suc (nk, _) -> (
      let (Suc (s, g, i)) = s in
      match deg_perm_of_plus nk s with
      | None_deg_perm_of_plus -> None_deg_perm_of_plus
      | Deg_perm_of_plus (mk, s, p) -> (
          match D.insert_into_plus g mk i with
          | Left _ -> None_deg_perm_of_plus
          | Right (j, mk') -> Deg_perm_of_plus (mk', s, Suc (p, g, j))))

(* A permutation with specified domain only *)
type _ perm_to = Perm_to : ('a, 'b) perm -> 'a perm_to
