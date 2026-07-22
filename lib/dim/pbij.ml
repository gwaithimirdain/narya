open Util
open Tlist
open Tbwd
open Signatures
open Singleton
open Deg
open Insertion
open Shuffle

(* A partial bijection is an insertion together with a shuffle.  Specifically, a partial bijection from a dimension 'evaluation to a dimension 'intrinsic consists of:
   - A dimension 'shared (the part of each that are bijective)
   - An insertion of 'shared into another dimension 'result to obtain 'evaluation.  This performs the permutation of 'shared.
   - A shuffle of 'shared into another dimension 'remaining to produce 'intrinsic.
   We currently parametrize a partial bijection by 'evaluation (the domain), 'intrinsic (the codomain), and 'remaining.  We haven't needed the others so far. *)

type (_, _, _) pbij =
  | Pbij :
      ('evaluation, 'result, 'shared) insertion * ('remaining, 'shared, 'intrinsic) shuffle
      -> ('evaluation, 'intrinsic, 'remaining) pbij

let dom_pbij : type e i r. (e, i, r) pbij -> e D.t = fun (Pbij (ins, _)) -> dom_ins ins
let cod_pbij : type e i r. (e, i, r) pbij -> i D.t = fun (Pbij (_, shuf)) -> out_shuffle shuf
let remaining : type e i r. (e, i, r) pbij -> r D.t = fun (Pbij (_, shuf)) -> left_shuffle shuf

(* An insertion is a partial bijection with zero 'remaining. *)
let pbij_of_ins : type a b c. (a, b, c) insertion -> (a, c, D.zero) pbij =
 fun ins -> Pbij (ins, zero_shuffle (cod_right_ins ins))

type _ pbij_of = Pbij_of : ('evaluation, 'intrinsic, 'remaining) pbij -> 'evaluation pbij_of

(* A partial bijection from a given 'evaluation dimension can be represented by a list of integers and direction strings.  The length of the list is the codomain 'intrinsic.  The integers in the list represent 'shared and the strings represent 'remaining, with their positions in the list giving the shuffle, and the values of the integers specifying where to insert them (into some dimension 'result) to produce 'evaluation. *)
let rec pbij_of_int_strings : type e.
    e D.t -> [ `Int of int | `Str of string ] list -> e pbij_of option =
 fun e strs ->
  match strs with
  | [] -> Some (Pbij_of (Pbij (ins_zero e, Zero)))
  | `Int n :: strs -> (
      match D.insert_of_int e (n + 1) with
      | Some (Into (g, ix)) -> (
          let strs =
            List.map
              (function
                | `Int i ->
                    if i < n then `Int i
                    else if i > n then `Int (i - 1)
                    else raise (Invalid_argument "pbij_of_int_strings")
                | `Str str -> `Str str)
              strs in
          match pbij_of_int_strings (D.uninsert ix e) strs with
          | Some (Pbij_of (Pbij (ins, shuf))) ->
              Some (Pbij_of (Pbij (Suc (ins, g, ix), Right (g, shuf))))
          | None -> None)
      | Some _ -> .
      | None -> None)
  | `Str str :: strs when str = Endpoints.refl_string () -> (
      match pbij_of_int_strings e strs with
      | Some (Pbij_of (Pbij (ins, shuf))) -> Some (Pbij_of (Pbij (ins, Left (D.deg, shuf))))
      | None -> None)
  | `Str _ :: _ -> None

let pbij_of_strings : type e. e D.t -> string list -> e pbij_of option =
 fun e strs ->
  pbij_of_int_strings e
    (List.map
       (fun x ->
         match int_of_string_opt x with
         | Some i -> `Int i
         | None -> `Str x)
       strs)

let rec int_strings_of_pbij : type n i r. (n, i, r) pbij -> [ `Int of int | `Str of string ] list =
 fun (Pbij (ins, shuf)) ->
  match shuf with
  | Zero -> []
  | Left (_, shuf) -> `Str (Endpoints.refl_string ()) :: int_strings_of_pbij (Pbij (ins, shuf))
  | Right (_, shuf) ->
      let (Suc (ins, _, ix)) = ins in
      let x = Tbwd.int_of_insert ix + 1 in
      `Int x
      :: List.map
           (function
             | `Int i -> if i >= x then `Int (i + 1) else `Int i
             | `Str str -> `Str str)
           (int_strings_of_pbij (Pbij (ins, shuf)))

let strings_of_pbij : type n i r. (n, i, r) pbij -> string list =
 fun pbij ->
  List.map
    (function
      | `Str s -> s
      | `Int i -> string_of_int i)
    (int_strings_of_pbij pbij)

(* When representing that as a single string, we run all the integers and direction strings together with a single prefix . if the integers are all one-digit, otherwise we separate them by .s with a prefix .. *)
let string_of_pbij : type n i r. (n, i, r) pbij -> string =
 fun pbij ->
  let strs = strings_of_pbij pbij in
  if List.is_empty strs then ""
  else if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
    ".." ^ String.concat "." strs
  else "." ^ String.concat "" strs

let eq_of_zero_pbij : type i r. (D.zero, i, r) pbij -> (r, i) Eq.t = function
  | Pbij (Zero _, shuf) -> eq_of_shuffle_zero shuf

type (_, _, _) singleton_pbij =
  | Left : ('a, 'i, 'i) singleton_pbij
  | Right : ('a, 'apred, 'i) insertion -> ('a, 'i, D.zero) singleton_pbij

let singleton_pbij : type a i r. (a, i, r) pbij -> i is_singleton -> (a, i, r) singleton_pbij =
 fun p One ->
  match p with
  | Pbij (_, Left (_, Zero)) -> Left
  | Pbij (ins, Right (_, Zero)) -> Right ins

type (_, _) pbij_between =
  | Pbij_between :
      ('evaluation, 'intrinsic, 'remaining) pbij
      -> ('evaluation, 'intrinsic) pbij_between

(* Enumerate all the partial bijections from a given 'evaluation to a given 'intrinsic. *)
let all_pbij_between : type evaluation intrinsic.
    evaluation D.t -> intrinsic D.t -> (evaluation, intrinsic) pbij_between Seq.t =
 fun evaluation intrinsic ->
  let open Monad.Ops (Monad.Seq) in
  let* (Ins_of ins) = all_ins_of evaluation in
  let* (Of_right shuf) = all_shuffles_right (cod_right_ins ins) intrinsic in
  return (Pbij_between (Pbij (ins, shuf)))

(* An insertion can be composed with a degeneracy on the evaluation dimension to produce a partial bijection (the first two outputs together), with an induced degeneracy on the results. *)

type (_, _, _) deg_comp_ins =
  | Deg_comp_ins :
      ('evaluation, 'result, 'shared) insertion
      * ('remaining, 'shared, 'intrinsic) shuffle
      * ('old_result, 'result) deg
      -> ('evaluation, 'old_result, 'intrinsic) deg_comp_ins

let rec deg_comp_ins : type m n i res.
    (m, n) deg -> (m, res, i) insertion -> (n, res, i) deg_comp_ins =
 fun deg ins ->
  match ins with
  | Zero _ -> Deg_comp_ins (Zero (cod_deg deg), Zero, deg)
  | Suc (ins, g, i) -> (
      match deg_coresidual deg i with
      | Coresidual_zero deg ->
          let (Deg_comp_ins (ins, shuf, s)) = deg_comp_ins deg ins in
          Deg_comp_ins (ins, Left (g, shuf), s)
      | Coresidual_suc (deg, j) ->
          let (Deg_comp_ins (ins, shuf, s)) = deg_comp_ins deg ins in
          Deg_comp_ins (Suc (ins, g, j), Right (g, shuf), s))

(* A partial bijection can be composed with a degeneracy on the evaluation dimension to produce another partial bijection, with an induced degeneracy on the results. *)

type (_, _, _, _) deg_comp_pbij =
  | Deg_comp_pbij :
      ('evaluation, 'result, 'shared) insertion
      * ('remaining, 'shared, 'intrinsic) shuffle
      * ('old_result, 'result) deg
      * (('remaining, D.zero) Eq.t -> ('r, D.zero) Eq.t)
      -> ('evaluation, 'old_result, 'intrinsic, 'r) deg_comp_pbij

let rec deg_comp_pbij : type m n i res rem sh.
    (m, n) deg -> (m, res, sh) insertion -> (rem, sh, i) shuffle -> (n, res, i, rem) deg_comp_pbij =
 fun deg ins shuf ->
  match shuf with
  | Zero ->
      let (Zero _) = ins in
      Deg_comp_pbij (ins_zero (cod_deg deg), Zero, deg, fun _ -> Eq)
  | Left (g, shuf) ->
      let (Deg_comp_pbij (ins, shuf, s, _)) = deg_comp_pbij deg ins shuf in
      Deg_comp_pbij
        ( ins,
          Left (g, shuf),
          s,
          function
          | _ -> . )
  | Right (g, shuf) -> (
      let (Suc (ins, _, i)) = ins in
      match deg_coresidual deg i with
      | Coresidual_zero deg ->
          let (Deg_comp_pbij (ins, shuf, s, _)) = deg_comp_pbij deg ins shuf in
          Deg_comp_pbij
            ( ins,
              Left (g, shuf),
              s,
              function
              | _ -> . )
      | Coresidual_suc (deg, j) ->
          let (Deg_comp_pbij (ins, shuf, s, ifzero)) = deg_comp_pbij deg ins shuf in
          Deg_comp_pbij (Suc (ins, g, j), Right (g, shuf), s, ifzero))

(* This is like deg_comp_pbij (for the insertion only, so far), but for adding a constant on the left rather than acting by an arbitrary degeneracy (for evaluation rather that acting).  This allows it to return more detailed information.  The dimension 'r (new remaining) is the piece of 'i (intrinsic) that lands in 'm (new added dimension on the left), while 'h (new shared) is the part that lands in 'n, and 't is the part of 'm that doesn't come from 'r.  Note that the first two outputs together form an ('n, 'i, 'r) pbij; that's why this is in this file, even though it doesn't refer explicitly to pbij.  *)

type (_, _, _, _) unplus_ins =
  | Unplus_ins :
      ('n, 's, 'h) insertion
      * ('r, 'h, 'i) shuffle
      * ('m, 't, 'r) insertion
      * ('t, 's, 'olds) D.plus
      -> ('m, 'n, 'olds, 'i) unplus_ins

let rec unplus_ins : type m n mn s i.
    m D.t -> (m, n, mn) D.plus -> (mn, s, i) insertion -> (m, n, s, i) unplus_ins =
 fun m mn ins ->
  match ins with
  | Zero _ ->
      (* i=0, r=0, h=0, t=m, tn=mn, s=n *)
      Unplus_ins (Zero (D.plus_right mn), Zero, Zero m, mn)
  | Suc (ins', g, x) -> (
      match D.insert_in_plus mn x with
      | Left (x, mn') ->
          let (Unplus_ins (nsh, rhi, mtr, ts)) = unplus_ins (D.uninsert x m) mn' ins' in
          (* right-increment i and r, middle-increment m, keep s and h the same *)
          Unplus_ins (nsh, Left (g, rhi), Suc (mtr, g, x), ts)
      | Right (x, mn') ->
          let (Unplus_ins (nsh, rhi, mtr, ts)) = unplus_ins m mn' ins' in
          (* right-increment i and h and s, middle-increment n, keep m and r the same *)
          Unplus_ins (Suc (nsh, g, x), Right (g, rhi), mtr, ts))

type (_, _, _, _, _, _) unplus_pbij =
  | Unplus_pbij :
      ('n, 'news, 'newh) insertion
      * ('r, 'newh, 'i) shuffle
      * ('oldr, 'newr, 'r) shuffle
      * ('m, 't, 'newr) insertion
      * ('t, 'news, 'olds) D.plus
      -> ('m, 'n, 'olds, 'oldr, 'h, 'i) unplus_pbij

let unplus_pbij : type m n mn s i r h.
    m D.t ->
    (m, n, mn) D.plus ->
    (mn, s, h) insertion ->
    (r, h, i) shuffle ->
    (m, n, s, r, h, i) unplus_pbij =
 fun m mn ins shuf ->
  let (Unplus_ins (nsh, rhi, mtr, ts)) = unplus_ins m mn ins in
  let (Comp_shuffle_right (rr, rhi)) = comp_shuffle_right rhi shuf in
  Unplus_pbij (nsh, rhi, rr, mtr, ts)

(* Convert a pbij to an insertion by increasing the evaluation dimension on the left to include the remaining dimension. *)
let rec ins_plus_of_pbij : type n s h r i rn.
    (n, s, h) insertion -> (r, h, i) shuffle -> (r, n, rn) D.plus -> (rn, s, i) insertion =
 fun ins shuf rn ->
  match shuf with
  | Zero ->
      let Eq = D.plus_uniq rn (D.zero_plus (dom_ins ins)) in
      ins
  | Right (g, shuf') ->
      let (Suc (ins', _, x)) = ins in
      let (Plus rn') = D.plus (D.uninsert x (dom_ins ins)) in
      Suc (ins_plus_of_pbij ins' shuf' rn', g, D.plus_insert rn' rn x)
  | Left (g, shuf') ->
      let (Insert_plus (rn', x)) = D.insert_plus Now rn in
      Suc (ins_plus_of_pbij ins shuf' rn', g, x)

(* Intrinsically well-typed maps with partial bijections as keys.  Each map has a fixed 'evaluation dimension and 'intrinsic dimension, but the 'result, 'shared, and 'remaining dimensions vary with the keys and values.  The values are parametrized by the 'remaining dimension as well as by an extra parameter that the map depends on; hence the whole notion of map is a functor parametrized by a Fam2.

   The definition of the map type involves itself recursively inside a Tuple, so we need a recursive module to tie that knot.  Recursive functors are not really implemented (in general they give "unsafe" errors), but there seems to be an exception that allows them as long as the recursive module call is never named or opened, though it can occur inline in a type definition (but not a function definition, since inline functor applications cannot appear in code).  Thus, it works to first define a recursive functor for just the necessary types and modules, and then another (non-recursive) functor that includes it and defines the operations. *)

module rec Internal_Pbijmap : functor (F : Fam2) -> sig
  module Param : sig
    type (_, _) t =
      | Sub :
          ('evaluation, 'intrinsic, 's, 'v) Internal_Pbijmap(F).gt
          -> ('evaluation, ('intrinsic * 's) * 'v) t
  end

  module Tup : module type of Tuple.Make (D.G) (Param)

  type (_, _, _, _) gt =
    | Zero : (D.zero, 's, 'r) D.bplus * ('r, 'v) F.t -> ('evaluation, D.zero, 's, 'v) gt
    | Suc : {
        g : 'g D.G.t;
        left : ('evaluation, 'intrinsic, ('g, 's) cons, 'v) gt;
        right : ('evaluation, 'g, ('intrinsic * 's) * 'v) Tup.t;
      }
        -> ('evaluation, ('intrinsic, 'g) D.suc, 's, 'v) gt

  type ('evaluation, 'intrinsic, 'v) t =
    ('evaluation, 'intrinsic, D.fwd_zero, 'v) gt * 'evaluation D.t
end =
functor
  (F : Fam2)
  ->
  struct
    (* The tuple of subtrees is parametrized by the generator 'g of the intrinsic dimension being shared, so that (see Tuple) it stores an actual subtree only at those positions whose generator matches, and only an apartness witness elsewhere; the latter keeps the maps marshallable and is handled entirely inside Tuple. *)
    module Param = struct
      type (_, _) t =
        | Sub :
            ('evaluation, 'intrinsic, 's, 'v) Internal_Pbijmap(F).gt
            -> ('evaluation, ('intrinsic * 's) * 'v) t
    end

    module Tup = Tuple.Make (D.G) (Param)

    (* An element of ('evaluation, 'intrinsic, 'v) t is an intrinsically well-typed map that associates to every partial bijection between 'evaluation and 'intrinsic, with remaining dimension 'r, an element of ('r, 'v) F.t.  As with cubes, we define this in terms of a more general type ('evaluation, 'intrinsic, 's, 'v) gt, where 's is the word of remaining dimensions accumulated so far along the path from the root.  The intrinsic dimensions are processed from the outside in, so a newly remaining generator is added at the *inner* end of 's; since the accumulator is a *forwards* word, this is just a [cons] and the Suc node needs to store no witness for it (contrast the Branches of Cube).  At a leaf, the accumulated forwards word 's is finally reconciled with the actual backwards remaining dimension 'r via a bplus (i.e. Tbwd.append) onto the empty word, so that the stored value can live at the genuine dimension 'r. *)
    type (_, _, _, _) gt =
      (* The definition is by induction on the intrinsic dimension.  If that's zero, then we are at a leaf and we just store something of the appropriate type, together with the bplus reconciling the accumulated forwards word with the backwards dimension. *)
      | Zero : (D.zero, 's, 'r) D.bplus * ('r, 'v) F.t -> ('evaluation, D.zero, 's, 'v) gt
      (* If it's a successor, then the shuffle acting on that last element either sends it into the remaining dimensions or the shared ones.  Thus, we store one subtree with the newly remaining generator consed onto the accumulator, and a tuple of subtrees with the same accumulator, indexed by where the new shared element ends up in the evaluation dimension (and with the image removed from the evaluation dimension; the intrinsically well-typed map Tuple takes care of that). *)
      | Suc : {
          g : 'g D.G.t;
          left : ('evaluation, 'intrinsic, ('g, 's) cons, 'v) gt;
          right : ('evaluation, 'g, ('intrinsic * 's) * 'v) Tup.t;
        }
          -> ('evaluation, ('intrinsic, 'g) D.suc, 's, 'v) gt

    type ('evaluation, 'intrinsic, 'v) t =
      ('evaluation, 'intrinsic, D.fwd_zero, 'v) gt * 'evaluation D.t
  end

module Pbijmap (F : Fam2) = struct
  include Internal_Pbijmap (F)

  (* The intrinsic dimension is automatically a dimension. *)
  let rec gintrinsic : type evaluation intrinsic r v.
      (evaluation, intrinsic, r, v) gt -> intrinsic D.t = function
    | Zero _ -> D.zero
    | Suc { g; left; _ } -> D.suc (gintrinsic left) g

  let intrinsic : type evaluation intrinsic v. (evaluation, intrinsic, v) t -> intrinsic D.t =
   fun (ms, _) -> gintrinsic ms

  type (_, _) wrapped = Wrap : ('evaluation, 'intrinsic, 'v) t -> ('evaluation, 'v) wrapped

  (* The carried bplus relation (r2, s, r) records that the key's not-yet-processed remaining dimensions r2 (a backwards word) sit inside the accumulated forwards word s, with total remaining r (backwards): r = r2 ++ s.  At each Left step the newly remaining generator moves from the inner end of r2 to the head of s, which is exactly one application of Append_cons. *)
  let rec gfind : type evaluation intrinsic s r2 r v.
      (evaluation, intrinsic, r2) pbij ->
      (evaluation, intrinsic, s, v) gt ->
      (r2, s, r) D.bplus ->
      (r, v) F.t =
   fun p m r12 ->
    match (p, m) with
    | Pbij (Zero _, Zero), Zero (bp, v) ->
        let Eq = D.bplus_uniq bp r12 in
        v
    | Pbij (ins, Left (_, shuf)), Suc m -> gfind (Pbij (ins, shuf)) m.left (Append_cons r12)
    | Pbij (Suc (ins, _, i), Right (_, shuf)), Suc m ->
        let (Sub m') = Tup.find i m.right in
        gfind (Pbij (ins, shuf)) m' r12

  let find : type evaluation intrinsic remaining v.
      (evaluation, intrinsic, remaining) pbij -> (evaluation, intrinsic, v) t -> (remaining, v) F.t
      =
   fun p (m, _) -> gfind p m Append_nil

  let rec gset : type evaluation intrinsic s r2 r v.
      (evaluation, intrinsic, r2) pbij ->
      (r, v) F.t ->
      (evaluation, intrinsic, s, v) gt ->
      (r2, s, r) D.bplus ->
      (evaluation, intrinsic, s, v) gt =
   fun p v m r12 ->
    match (p, m) with
    | Pbij (Zero _, Zero), Zero _ -> Zero (r12, v)
    | Pbij (ins, Left (_, shuf)), Suc m ->
        Suc { m with left = gset (Pbij (ins, shuf)) v m.left (Append_cons r12) }
    | Pbij (Suc (ins, _, i), Right (_, shuf)), Suc m ->
        Suc
          {
            m with
            right = Tup.update i (fun (Sub m') -> Sub (gset (Pbij (ins, shuf)) v m' r12)) m.right;
          }

  let set : type evaluation intrinsic remaining v.
      (evaluation, intrinsic, remaining) pbij ->
      (remaining, v) F.t ->
      (evaluation, intrinsic, v) t ->
      (evaluation, intrinsic, v) t =
   fun p v (m, e) -> (gset p v m Append_nil, e)

  let find_singleton : type evaluation intrinsic v.
      (evaluation, intrinsic, v) t -> (D.zero, v) F.t option = function
    | Zero (Append_nil, v), _ -> Some v
    | Suc _, _ -> None

  type ('evaluation, 'intrinsic, 's, 'v) gbuilder = {
    remaining : 's D.fwd;
    build : 'r2 'r. ('evaluation, 'intrinsic, 'r2) pbij -> ('r2, 's, 'r) D.bplus -> ('r, 'v) F.t;
  }

  let rec gbuild : type evaluation intrinsic s v.
      evaluation D.t ->
      intrinsic D.t ->
      (evaluation, intrinsic, s, v) gbuilder ->
      (evaluation, intrinsic, s, v) gt =
   fun evaluation intrinsic f ->
    match intrinsic with
    | Word Zero ->
        let (Bplus bp) = D.bplus f.remaining in
        Zero (bp, f.build (Pbij (ins_zero evaluation, Zero)) bp)
    | Word (Suc (type i1 g0t) ((intrinsic, g_intrinsic) : (_, i1, _) D.plus * g0t D.G.t)) ->
        Suc
          {
            g = g_intrinsic;
            left =
              gbuild evaluation (Word intrinsic)
                {
                  remaining = D.Cons (g_intrinsic, f.remaining);
                  build =
                    (fun (Pbij (ins, shuf)) r12 ->
                      let (Append_cons r12') = r12 in
                      f.build (Pbij (ins, Left (g_intrinsic, shuf))) r12');
                };
            right =
              (let build : type b. (b, g0t, evaluation) Tbwd.insert -> (b, (i1 * s) * v) Param.t =
                fun i ->
                 Sub
                   (gbuild (D.uninsert i evaluation) (Word intrinsic)
                      {
                        f with
                        build =
                          (fun (Pbij (ins, shuf)) r12 ->
                            f.build
                              (Pbij (Suc (ins, g_intrinsic, i), Right (g_intrinsic, shuf)))
                              r12);
                      }) in
               Tup.build evaluation g_intrinsic { build });
          }

  type ('evaluation, 'intrinsic, 'v) builder = {
    build : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'v) F.t;
  }

  let gbuilder_of_builder : type evaluation intrinsic v r2 r.
      (evaluation, intrinsic, v) builder ->
      (evaluation, intrinsic, r2) pbij ->
      (r2, D.fwd_zero, r) D.bplus ->
      (r, v) F.t =
   fun f p r12 ->
    let Append_nil = r12 in
    f.build p

  let build : type evaluation intrinsic v.
      evaluation D.t ->
      intrinsic D.t ->
      (evaluation, intrinsic, v) builder ->
      (evaluation, intrinsic, v) t =
   fun evaluation intrinsic f ->
    ( gbuild evaluation intrinsic
        { remaining = D.fwd_zero; build = (fun p r12 -> gbuilder_of_builder f p r12) },
      evaluation )

  let singleton : type evaluation v. evaluation D.t -> (D.zero, v) F.t -> (evaluation, D.zero, v) t
      =
   fun e v -> (Zero (Append_nil, v), e)

  (* Generic traversal *)

  module Times = struct
    type (_, _, _) t = Times : ('p, 'x, 'p * 'x) t
    type (_, _) exists = Exists : ('p, 'a, 'b) t -> ('p, 'a) exists

    let exists : ('p, 'a) exists = Exists Times
  end

  module MapTimes = Tlist.Map (Times)

  module Heter = struct
    type (_, _) hft =
      | [] : ('a, nil) hft
      | ( :: ) : ('a, 'v) F.t * ('a, 'vs) hft -> ('a, ('v, 'vs) cons) hft

    type (_, _, _, _) hgt =
      | [] : ('e, 'i, 'r, nil) hgt
      | ( :: ) : ('e, 'i, 'r, 'v) gt * ('e, 'i, 'r, 'vs) hgt -> ('e, 'i, 'r, ('v, 'vs) cons) hgt

    let rec zero : type s r e vs. (D.zero, s, r) D.bplus -> (r, vs) hft -> (e, D.zero, s, vs) hgt =
     fun bp -> function
      | [] -> []
      | v :: vs -> Zero (bp, v) :: zero bp vs

    let rec suc : type e i s g vs irvs.
        g D.G.t ->
        (e, i, (g, s) cons, vs) hgt ->
        (i * s, vs, irvs) MapTimes.t ->
        (e, nil, g, irvs) Tup.Heter.hgt ->
        (e, (i, g) D.suc, s, vs) hgt =
     fun g ls irvs rs ->
      match (ls, irvs, rs) with
      | [], [], [] -> []
      | left :: ls, Times :: irvs, right :: rs -> Suc { g; left; right } :: suc g ls irvs rs

    let rec zeros : type e s r vs. (D.zero, s, r) D.bplus -> (e, D.zero, s, vs) hgt -> (r, vs) hft =
     fun bp -> function
      | [] -> []
      | Zero (bp', v) :: ms ->
          let Eq = D.bplus_uniq bp' bp in
          v :: zeros bp ms

    let rec left : type e i s g vs. (e, (i, g) D.suc, s, vs) hgt -> (e, i, (g, s) cons, vs) hgt =
     fun ms ->
      match ms with
      | [] -> []
      | Suc { left = l; _ } :: ms -> l :: left ms

    let rec right : type e i r g vs irvs.
        (e, (i, g) D.suc, r, vs) hgt ->
        (i * r, vs, irvs) MapTimes.t ->
        (e, nil, g, irvs) Tup.Heter.hgt =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | Suc { right = r; _ } :: ms, Times :: irvs -> r :: right ms irvs

    let rec wrap : type e i r vs irvs.
        (e, i, r, vs) hgt -> (i * r, vs, irvs) MapTimes.t -> (e, irvs) Tup.Heter.hft =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | m :: ms, Times :: irvs -> Sub m :: wrap ms irvs

    let rec unwrap : type e i r vs irvs.
        (e, irvs) Tup.Heter.hft -> (i * r, vs, irvs) MapTimes.t -> (e, i, r, vs) hgt =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | Sub m :: ms, Times :: irvs -> m :: unwrap ms irvs

    let rec params : type e i r vs. (e, i, r, vs) hgt -> vs Tlist.t = function
      | [] -> Nil
      | _ :: vs -> Cons (params vs)

    type (_, _, _) ht =
      | [] : ('e, 'i, nil) ht
      | ( :: ) : ('e, 'i, 'v) t * ('e, 'i, 'vs) ht -> ('e, 'i, ('v, 'vs) cons) ht

    let rec hgt_of_ht : type e i vs. (e, i, vs) ht -> (e, i, D.fwd_zero, vs) hgt = function
      | [] -> []
      | (m, _) :: ms -> m :: hgt_of_ht ms

    let rec ht_of_hgt : type e i vs. (e, i, D.fwd_zero, vs) hgt -> e D.t -> (e, i, vs) ht =
     fun ms e ->
      match ms with
      | [] -> []
      | m :: ms -> (m, e) :: ht_of_hgt ms e
  end

  type ('evaluation, 'intrinsic, 's, 'vs, 'ws) gpmapper = {
    remaining : 's D.fwd;
    map :
      'r2 'r.
      ('evaluation, 'intrinsic, 'r2) pbij ->
      ('r2, 's, 'r) D.bplus ->
      ('r, 'vs) Heter.hft ->
      ('r, 'ws) Heter.hft;
  }

  let rec gpmap : type evaluation intrinsic remaining v vs ws.
      evaluation D.t ->
      (evaluation, intrinsic, remaining, (v, vs) cons, ws) gpmapper ->
      (evaluation, intrinsic, remaining, (v, vs) cons) Heter.hgt ->
      ws Tlist.t ->
      (evaluation, intrinsic, remaining, ws) Heter.hgt =
   fun evaluation f ms ws ->
    match ms with
    | Zero _ :: _ ->
        let (Bplus bp) = D.bplus f.remaining in
        let res = f.map (Pbij (ins_zero evaluation, Zero)) bp (Heter.zeros bp ms) in
        Heter.zero bp res
    | Suc { g = g_outer; _ } :: _ -> gpmap_suc evaluation g_outer f ms ws

  and gpmap_suc : type evaluation i1 g0t s v vs ws.
      evaluation D.t ->
      g0t D.G.t ->
      (evaluation, (i1, g0t) D.suc, s, (v, vs) cons, ws) gpmapper ->
      (evaluation, (i1, g0t) D.suc, s, (v, vs) cons) Heter.hgt ->
      ws Tlist.t ->
      (evaluation, (i1, g0t) D.suc, s, ws) Heter.hgt =
   fun evaluation g_outer f ms ws ->
    let (Exists_cons irvs) = MapTimes.exists_cons (Heter.params ms) in
    let irvs : (i1 * s, (v, vs) cons, _) MapTimes.t = irvs in
    let (Exists irws) = MapTimes.exists ws in
    let irws : (i1 * s, ws, _) MapTimes.t = irws in
    let map : type a.
        (a, g0t, evaluation) Tbwd.insert -> (a, _) Tup.Heter.hft -> (a, _) Tup.Heter.hft =
     fun i x ->
      let res =
        gpmap (D.uninsert i evaluation)
          {
            f with
            map =
              (fun (Pbij (ins, shuf)) r12 v ->
                f.map (Pbij (Suc (ins, g_outer, i), Right (g_outer, shuf))) r12 v);
          }
          (Heter.unwrap x irvs) ws in
      Heter.wrap res irws in
    let lefts =
      gpmap evaluation
        {
          remaining = D.Cons (g_outer, f.remaining);
          map =
            (fun (Pbij (ins, shuf)) r12 v ->
              let (Append_cons r12') = r12 in
              f.map (Pbij (ins, Left (g_outer, shuf))) r12' v);
        }
        (Heter.left ms) ws in
    let rights = Tup.pmap { map } (Heter.right ms irvs) (MapTimes.cod irws) in
    Heter.suc g_outer lefts irws rights

  type ('evaluation, 'intrinsic, 'vs, 'ws) pmapper = {
    map : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'vs) Heter.hft -> ('r, 'ws) Heter.hft;
  }

  let gpmapper_of_pmapper : type evaluation intrinsic vs ws r2 r.
      (evaluation, intrinsic, vs, ws) pmapper ->
      (evaluation, intrinsic, r2) pbij ->
      (r2, D.fwd_zero, r) D.bplus ->
      (r, vs) Heter.hft ->
      (r, ws) Heter.hft =
   fun f p r12 ->
    let Append_nil = r12 in
    f.map p

  let pmap : type evaluation intrinsic v vs ws.
      (evaluation, intrinsic, (v, vs) cons, ws) pmapper ->
      (evaluation, intrinsic, (v, vs) cons) Heter.ht ->
      ws Tlist.t ->
      (evaluation, intrinsic, ws) Heter.ht =
   fun f ((_, e) :: _ as ms) ws ->
    let res =
      gpmap e
        { remaining = D.fwd_zero; map = (fun p r12 -> gpmapper_of_pmapper f p r12) }
        (Heter.hgt_of_ht ms) ws in
    Heter.ht_of_hgt res e

  type ('evaluation, 'intrinsic, 'vs, 'w) mmapper = {
    map : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'vs) Heter.hft -> ('r, 'w) F.t;
  }

  let mmap f xs =
    let [ ys ] =
      pmap
        {
          map =
            (fun i x ->
              let y = f.map i x in
              [ y ]);
        }
        xs (Cons Nil) in
    ys

  type ('evaluation, 'intrinsic, 'vs) miterator = {
    it : 'r. ('evaluation, 'intrinsic, 'r) pbij -> ('r, 'vs) Heter.hft -> unit;
  }

  let miter f xs =
    let [] =
      pmap
        {
          map =
            (fun i x ->
              f.it i x;
              []);
        }
        xs Nil in
    ()
end

module PbijmapOf = Pbijmap (struct
  type ('a, 'b) t = 'b
end)
