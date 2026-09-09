open Util
open Deg
open Perm

(* A shuffle is a permutation of a sum that preserves the relative order of *both* inputs.  Specifically, an ('a, 'b, 'c) shuffle shuffles the two inputs 'a and 'b together to produce 'c. *)

type (_, _, _) shuffle =
  | Zero : (D.zero, D.zero, D.zero) shuffle
  | Left : 'g D.G.t * ('a, 'b, 'ab) shuffle -> (('a, 'g) D.suc, 'b, ('ab, 'g) D.suc) shuffle
  | Right : 'g D.G.t * ('a, 'b, 'ab) shuffle -> ('a, ('b, 'g) D.suc, ('ab, 'g) D.suc) shuffle

let rec perm_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) perm =
 fun s ab ->
  match s with
  | Zero ->
      let Zero = ab in
      Zero
  | Left (g, s) ->
      let (Strip_plus_left (inner_plus, i)) = D.strip_plus_left g ab in
      perm_with_extra (perm_of_shuffle s inner_plus) g i
  | Right (g, s) ->
      let (Suc (ab, _)) = ab in
      Suc (perm_of_shuffle s ab, g, Now)

(* Hence a shuffle also induces a degeneracy. *)
let deg_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) deg =
 fun s ab -> deg_of_perm (perm_of_shuffle s ab)

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

(* Are two shuffles equal?  If so, all three of their parameters are identified. *)
let rec equal_shuffle : type a1 b1 c1 a2 b2 c2.
    (a1, b1, c1) shuffle -> (a2, b2, c2) shuffle -> (a1 * b1 * c1, a2 * b2 * c2) Eq.t option =
 fun s1 s2 ->
  match (s1, s2) with
  | Zero, Zero -> Some Eq
  | Left (g1, s1), Left (g2, s2) -> (
      match (equal_shuffle s1 s2, D.G.compare g1 g2) with
      | Some Eq, Eq -> Some Eq
      | _ -> None)
  | Right (g1, s1), Right (g2, s2) -> (
      match (equal_shuffle s1 s2, D.G.compare g1 g2) with
      | Some Eq, Eq -> Some Eq
      | _ -> None)
  | _ -> None

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

(* Conversely, if 'ab is a shuffle of 'a and 'b, and 'abc is a shuffle of that with 'c, then we can reassociate: 'b and 'c shuffle to some 'bc, which shuffles with 'a to give 'abc. *)

type (_, _, _, _) comp_shuffle_left =
  | Comp_shuffle_left :
      ('b, 'c, 'bc) shuffle * ('a, 'bc, 'abc) shuffle
      -> ('a, 'b, 'c, 'abc) comp_shuffle_left

let rec comp_shuffle_left : type a b ab c abc.
    (a, b, ab) shuffle -> (ab, c, abc) shuffle -> (a, b, c, abc) comp_shuffle_left =
 fun ab abc ->
  match abc with
  (* If 'abc is empty, so are 'ab and 'c, hence also 'a and 'b. *)
  | Zero ->
      let Zero = ab in
      Comp_shuffle_left (Zero, Zero)
  (* If the outermost element of 'abc comes from 'c, it belongs to 'bc, and hence appears on the right in both output shuffles. *)
  | Right (g, abc) ->
      let (Comp_shuffle_left (bc, abc)) = comp_shuffle_left ab abc in
      Comp_shuffle_left (Right (g, bc), Right (g, abc))
  (* Otherwise it comes from 'ab, and we ask that shuffle where it came from. *)
  | Left (g, abc) -> (
      match ab with
      (* If from 'a, it doesn't belong to 'bc, and appears on the left of the outer output shuffle. *)
      | Left (_, ab) ->
          let (Comp_shuffle_left (bc, abc)) = comp_shuffle_left ab abc in
          Comp_shuffle_left (bc, Left (g, abc))
      (* If from 'b, it belongs to 'bc on the left, and hence to the right of the outer output shuffle. *)
      | Right (_, ab) ->
          let (Comp_shuffle_left (bc, abc)) = comp_shuffle_left ab abc in
          Comp_shuffle_left (Left (g, bc), Right (g, abc)))

type (_, _) shuffle_right = Of_right : ('a, 'b, 'c) shuffle -> ('b, 'c) shuffle_right

let rec all_shuffles_right : type b c. b D.t -> c D.t -> (b, c) shuffle_right Seq.t =
 fun b c ->
  match b with
  | Word Zero -> Seq.cons (Of_right (shuffle_zero c)) Seq.empty
  | Word (Suc (b', g_b)) -> (
      match c with
      | Word Zero -> Seq.empty
      | Word (Suc (c', g_c)) -> (
          (* Left g_c (consuming a's outer, leaving b unchanged) is always available regardless of g_b: [Left]'s a is existential. *)
          let left_options =
            Seq.map
              (fun (Of_right s) -> Of_right (Left (g_c, s)))
              (all_shuffles_right (Word (Suc (b', g_b))) (Word c')) in
          (* Right g_c requires b's outer generator to be g_c: this is a genuine check, not a bridge. *)
          match D.G.compare g_b g_c with
          | Neq -> left_options
          | Eq ->
              Seq.append left_options
                (Seq.map
                   (fun (Of_right s) -> Of_right (Right (g_c, s)))
                   (all_shuffles_right (Word b') (Word c')))))
