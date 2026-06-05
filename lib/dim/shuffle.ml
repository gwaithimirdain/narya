open Util
open Deg
open Perm

(* A shuffle is a permutation of a sum that preserves the relative order of *both* inputs.  Specifically, an ('a, 'b, 'c) shuffle shuffles the two inputs 'a and 'b together to produce 'c. *)

type (_, _, _) shuffle =
  | Zero : (D.zero, D.zero, D.zero) shuffle
  | Left :
      'g D.G.t * ('a, 'b, 'ab) shuffle
      -> (('a, 'g) D.suc, 'b, ('ab, 'g) D.suc) shuffle
  | Right :
      'g D.G.t * ('a, 'b, 'ab) shuffle
      -> ('a, ('b, 'g) D.suc, ('ab, 'g) D.suc) shuffle

let rec plus_of_shuffle : type a b c. (a, b, c) shuffle -> (a, b, c) D.plus = function
  | Zero -> Zero
  | Left (g, s) -> (
      (* TODO: bridge via G.compare; D.suc_plus_eq_suc still hardcodes unit. *)
      match D.G.compare g D.deg with
      | Neq -> assert false
      | Eq -> D.suc_plus_eq_suc (plus_of_shuffle s))
  | Right (g, s) -> Suc (plus_of_shuffle s, g)

let rec deg_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) deg =
 fun s ab ->
  match s with
  | Zero ->
      let Zero = ab in
      Zero D.zero
  | Left (g, s) -> (
      match D.G.compare g D.deg with
      | Neq -> assert false
      | Eq ->
          let (Suc (ab, Unit)) = D.plus_suc ab in
          Suc (deg_of_shuffle s ab, g, Now))
  | Right (g, s) ->
      let (Suc (ab, _)) = ab in
      Suc (deg_of_shuffle s ab, g, Now)

let rec perm_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) perm =
 fun s ab ->
  match s with
  | Zero ->
      let Zero = ab in
      Zero
  | Left (g, s) -> (
      match D.G.compare g D.deg with
      | Neq -> assert false
      | Eq ->
          let (Suc (ab, Unit)) = D.plus_suc ab in
          Suc (perm_of_shuffle s ab, g, Now))
  | Right (g, s) ->
      let (Suc (ab, _)) = ab in
      Suc (perm_of_shuffle s ab, g, Now)

let rec left_shuffle : type a b c. (a, b, c) shuffle -> a D.t = function
  | Zero -> D.zero
  | Left (g, s) -> D.suc (left_shuffle s) g
  | Right (_, s) -> left_shuffle s

let rec right_shuffle : type a b c. (a, b, c) shuffle -> b D.t = function
  | Zero -> D.zero
  | Left (_, s) -> right_shuffle s
  | Right (g, s) -> D.suc (right_shuffle s) g

let rec out_shuffle : type a b c. (a, b, c) shuffle -> c D.t = function
  | Zero -> D.zero
  | Left (g, s) -> D.suc (out_shuffle s) g
  | Right (g, s) -> D.suc (out_shuffle s) g

let rec shuffle_zero : type a. a D.t -> (a, D.zero, a) shuffle = function
  | Word Zero -> Zero
  | Word (Suc (a, g)) -> Left (g, shuffle_zero (Word a))

let rec zero_shuffle : type a. a D.t -> (D.zero, a, a) shuffle = function
  | Word Zero -> Zero
  | Word (Suc (a, g)) -> Right (g, zero_shuffle (Word a))

let rec eq_of_zero_shuffle : type a b. (D.zero, a, b) shuffle -> (a, b) Eq.t = function
  | Zero -> Eq
  | Right (_, s) ->
      let Eq = eq_of_zero_shuffle s in
      Eq

let rec eq_of_shuffle_zero : type a b. (a, D.zero, b) shuffle -> (a, b) Eq.t = function
  | Zero -> Eq
  | Left (_, s) ->
      let Eq = eq_of_shuffle_zero s in
      Eq

type (_, _, _, _) comp_shuffle_right =
  | Comp_shuffle_right :
      ('a, 'b, 'ab) shuffle * ('ab, 'c, 'abc) shuffle
      -> ('a, 'b, 'c, 'abc) comp_shuffle_right

let rec comp_shuffle_right : type a b c bc abc.
    (b, c, bc) shuffle -> (a, bc, abc) shuffle -> (a, b, c, abc) comp_shuffle_right =
 fun bc abc ->
  match (bc, abc) with
  | Zero, _ ->
      let Eq = eq_of_shuffle_zero abc in
      Comp_shuffle_right (shuffle_zero (left_shuffle abc), abc)
  | _, Left (g, abc) ->
      let (Comp_shuffle_right (ab, abc')) = comp_shuffle_right bc abc in
      Comp_shuffle_right (Left (g, ab), Left (g, abc'))
  | Left (g, bc), Right (g', abc) ->
      let (Comp_shuffle_right (ab, abc')) = comp_shuffle_right bc abc in
      Comp_shuffle_right (Right (g', ab), Left (g, abc'))
  | Right (g, bc), Right (_, abc) ->
      let (Comp_shuffle_right (ab, abc')) = comp_shuffle_right bc abc in
      Comp_shuffle_right (ab, Right (g, abc'))

type (_, _) shuffle_right = Of_right : ('a, 'b, 'c) shuffle -> ('b, 'c) shuffle_right

let rec all_shuffles_right : type b c. b D.t -> c D.t -> (b, c) shuffle_right Seq.t =
 fun b c ->
  match b with
  | Word Zero -> Seq.cons (Of_right (shuffle_zero c)) Seq.empty
  | Word (Suc (b', g_b)) -> (
      match c with
      | Word Zero -> Seq.empty
      | Word (Suc (c', g_c)) -> (
          (* g_b and g_c must agree for [Right] to extend b's word: bridge via G.compare. *)
          match D.G.compare g_b g_c with
          | Neq -> Seq.empty
          | Eq ->
              Seq.append
                (Seq.map
                   (fun (Of_right s) -> Of_right (Left (g_c, s)))
                   (all_shuffles_right (Word (Suc (b', g_b))) (Word c')))
                (Seq.map
                   (fun (Of_right s) -> Of_right (Right (g_c, s)))
                   (all_shuffles_right (Word b') (Word c')))))
