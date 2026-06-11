open Util
open Deg
open Perm

(* A shuffle is a permutation of a sum that preserves the relative order of *both* inputs.  Specifically, an ('a, 'b, 'c) shuffle shuffles the two inputs 'a and 'b together to produce 'c. *)

type (_, _, _) shuffle =
  | Zero : (D.zero, D.zero, D.zero) shuffle
  | Left : 'g D.G.t * ('a, 'b, 'ab) shuffle -> (('a, 'g) D.suc, 'b, ('ab, 'g) D.suc) shuffle
  | Right : 'g D.G.t * ('a, 'b, 'ab) shuffle -> ('a, ('b, 'g) D.suc, ('ab, 'g) D.suc) shuffle

(* [plus_of_shuffle : (a, b, c) shuffle -> (a, b, c) D.plus] would claim that c = a + b at the type level.  In a single-generator world that's tautological, but for multi-generator words the shuffle's c is a specific interleaving while a + b is the canonical concatenation, and they're different word-types in general.  The function only made sense in single-direction; removed in Phase 7a.  No external callers used it. *)

(* Strip the leftmost g from a [((m, g) suc, n, p) plus]: returns the inner [(m, n, p_inner) plus] and an insertion that recovers p as p_inner with g inserted at the appropriate position.  Inducts on n's plus structure, no commutativity required. *)
type (_, _, _, _) strip_left_g =
  | Strip_left_g : ('m, 'n, 'q) D.plus * ('q, 'g, 'p) D.insert -> ('m, 'g, 'n, 'p) strip_left_g

let rec strip_left_g : type m g n p.
    g D.G.t -> ((m, g) D.suc, n, p) D.plus -> (m, g, n, p) strip_left_g =
 fun g -> function
  | Zero -> Strip_left_g (Zero, Now)
  | Suc (ab, h) ->
      let (Strip_left_g (q, i)) = strip_left_g g ab in
      Strip_left_g (Suc (q, h), Later i)

(* Extend a deg [(c, ab) deg] by a new codomain element g inserted at a specified position in ab.  The new element corresponds to a new outermost domain element.  Inducts on the insertion position. *)
let rec deg_with_extra : type c ab ab_suc g.
    (c, ab) deg -> g D.G.t -> (ab, g, ab_suc) D.insert -> ((c, g) D.suc, ab_suc) deg =
 fun d g i ->
  match i with
  | Now -> Suc (d, g, Now)
  | Later j ->
      let (Suc (d_inner, h, ins_d)) = d in
      Suc (deg_with_extra d_inner g j, h, Later ins_d)

let rec perm_with_extra : type c ab ab_suc g.
    (c, ab) perm -> g D.G.t -> (ab, g, ab_suc) D.insert -> ((c, g) D.suc, ab_suc) perm =
 fun p g i ->
  match i with
  | Now -> Suc (p, g, Now)
  | Later j ->
      let (Suc (p_inner, h, ins_p)) = p in
      Suc (perm_with_extra p_inner g j, h, Later ins_p)

let rec deg_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) deg =
 fun s ab ->
  match s with
  | Zero ->
      let Zero = ab in
      Zero D.zero
  | Left (g, s) ->
      let (Strip_left_g (inner_plus, i)) = strip_left_g g ab in
      deg_with_extra (deg_of_shuffle s inner_plus) g i
  | Right (g, s) ->
      let (Suc (ab, _)) = ab in
      Suc (deg_of_shuffle s ab, g, Now)

let rec perm_of_shuffle : type a b c ab. (a, b, c) shuffle -> (a, b, ab) D.plus -> (c, ab) perm =
 fun s ab ->
  match s with
  | Zero ->
      let Zero = ab in
      Zero
  | Left (g, s) ->
      let (Strip_left_g (inner_plus, i)) = strip_left_g g ab in
      perm_with_extra (perm_of_shuffle s inner_plus) g i
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
