open Signatures
open Tbwd

(* Type-level free categories. *)

module type Quiver = sig
  module Obj : Comparable

  type ('src, 'g, 'tgt) t

  val src : ('src, 'g, 'tgt) t -> 'src Obj.t
  val tgt : ('src, 'g, 'tgt) t -> 'tgt Obj.t
  val src_uniq : ('src1, 'g, 'tgt1) t -> ('src2, 'g, 'tgt2) t -> ('src1, 'src2) Eq.t
  val tgt_uniq : ('src1, 'g, 'tgt1) t -> ('src2, 'g, 'tgt2) t -> ('tgt1, 'tgt2) Eq.t

  val compare :
    ('d1, 'g1, 'c1) t -> ('d2, 'g2, 'c2) t -> ('d1 * 'g1 * 'c1, 'd2 * 'g2 * 'c2) Eq.compare
end

module type Quivermap = sig
  module Dom : Quiver
  module Cod : Quiver
  module Obj : Function with module Dom = Dom.Obj and module Cod = Cod.Obj

  type (_, _, _, _, _, _) t

  val dom : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) Dom.t
  val cod : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('x, 'n, 'y) Cod.t
  val src : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'x) Obj.t
  val tgt : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('b, 'y) Obj.t

  type (_, _, _) exists = Exists : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) exists

  val exists : ('a, 'm, 'b) Dom.t -> ('a, 'm, 'b) exists

  val uniq :
    ('a, 'm, 'b, 'x1, 'n1, 'y1) t ->
    ('a, 'm, 'b, 'x2, 'n2, 'y2) t ->
    ('x1 * 'n1 * 'y1, 'x2 * 'n2 * 'y2) Eq.t
end

(* The free category on a quiver.  Its objects are those of the quiver, and its morphisms ("paths") are sequences of composable edges.  We follow the design of Word.Make: paths are represented as type-level backwards lists of edge-types (so we can append on the right efficiently), and composition is encoded as a relation. *)

module Make (Q : Quiver) = struct
  module Obj = Q.Obj

  (* The "shape" of a path is a type-level backwards list of generators.  As in Word, the list elements are just the edge-type indices; the source and target objects are tracked separately by the path itself. *)

  type zero = emp
  type ('n, 'g) suc = ('n, 'g) snoc

  (* ********** Composition ********** *)

  (* Composition is the analog of Word's addition.  ('a, 'm, 'b, 'n, 'c, 'p) comp says that a path from 'a to 'b of shape 'm composed with a path from 'b to 'c of shape 'n is a path from 'a to 'c of shape 'p.  As with Word, we never carry around the prefix path explicitly; the prefix shape and source are existential, witnessed by the existence of a comp relation. *)

  type (_, _, _, _, _, _) comp =
    | Zero : ('a, 'm, 'b, zero, 'b, 'm) comp
    | Suc :
        ('a, 'm, 'b, 'n, 'c, 'p) comp * ('c, 'g, 'd) Q.t
        -> ('a, 'm, 'b, ('n, 'g) suc, 'd, ('p, 'g) suc) comp

  (* A valid path from 'src to 'tgt of shape 'shape.  Following Word, this is "anything that can sit on the right of a composition"; we additionally remember the source object so that, e.g., the identity path can produce a target object on demand. *)

  type (_, _, _) t =
    | Path :
        'src Obj.t * ('any_a, 'any_m, 'src, 'shape, 'tgt, 'any_p) comp
        -> ('src, 'shape, 'tgt) t

  type wrapped = Wrap : ('src, 'shape, 'tgt) t -> wrapped

  (* Smart constructors *)

  let id : type a. a Obj.t -> (a, zero, a) t = fun a -> Path (a, Zero)

  let suc : type a m b g c. (a, m, b) t -> (b, g, c) Q.t -> (a, (m, g) suc, c) t =
   fun (Path (a, n)) g -> Path (a, Suc (n, g))

  (* ********** Source and target ********** *)

  let src : type a m b. (a, m, b) t -> a Obj.t = fun (Path (a, _)) -> a

  let tgt : type a m b. (a, m, b) t -> b Obj.t =
   fun (Path (a, p)) ->
    match p with
    | Zero -> a
    | Suc (_, g) -> Q.tgt g

  (* ********** Computing compositions ********** *)

  type (_, _, _, _, _) has_comp =
    | Comp : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b, 'n, 'c) has_comp

  let rec comp : type a m b n c. (b, n, c) t -> (a, m, b, n, c) has_comp = function
    | Path (_, Zero) -> Comp Zero
    | Path (b, Suc (n, g)) ->
        let (Comp mn) = comp (Path (b, n)) in
        Comp (Suc (mn, g))

  let rec comp_out : type a m b n c p. (a, m, b) t -> (a, m, b, n, c, p) comp -> (a, p, c) t =
   fun pm mn ->
    match mn with
    | Zero -> pm
    | Suc (mn, g) ->
        let p_mn = comp_out pm mn in
        suc p_mn g

  let comp_right : type a m b n c p. b Obj.t -> (a, m, b, n, c, p) comp -> (b, n, c) t =
   fun b mn -> Path (b, mn)

  let rec comp_left : type a m b n c p.
      (a, m, b, n, c, p) comp -> (a, p, c) t -> (a, m, b) t =
   fun ev result ->
    match (ev, result) with
    | Zero, _ -> result
    | Suc (ev, edge), Path (a, Suc (inner, edge')) ->
        let Eq = Q.src_uniq edge edge' in
        comp_left ev (Path (a, inner))

  let rec comp_uniq : type a m b n c p p'.
      (a, m, b, n, c, p) comp -> (a, m, b, n, c, p') comp -> (p, p') Eq.t =
   fun mn mn' ->
    match (mn, mn') with
    | Zero, Zero -> Eq
    | Suc (mn, edge), Suc (mn', edge') ->
        let Eq = Q.src_uniq edge edge' in
        let Eq = comp_uniq mn mn' in
        Eq

  (* ********** Unitality ********** *)

  let rec id_comp : type b n c. (b, n, c) t -> (b, zero, b, n, c, n) comp =
   fun n ->
    match n with
    | Path (_, Zero) -> Zero
    | Path (b, Suc (n_inner, g)) -> Suc (id_comp (Path (b, n_inner)), g)

  let comp_id : type a m b. (a, m, b) t -> (a, m, b, zero, b, m) comp = fun _ -> Zero

  (* ********** Associativity ********** *)

  (* Given evidence m·n=mn, n·p=np, and m·(n·p)=mnp, we get (m·n)·p=mnp. *)

  let rec comp_assocl : type a m b n c d p mn np mnp.
      (a, m, b, n, c, mn) comp ->
      (b, n, c, p, d, np) comp ->
      (a, m, b, np, d, mnp) comp ->
      (a, mn, c, p, d, mnp) comp =
   fun mn np m_np ->
    match np with
    | Zero ->
        let Eq = comp_uniq mn m_np in
        Zero
    | Suc (np_inner, edge) ->
        let (Suc (m_np_inner, edge')) = m_np in
        let Eq = Q.src_uniq edge edge' in
        let mn_p = comp_assocl mn np_inner m_np_inner in
        Suc (mn_p, edge)

  (* The reverse direction: given m·n=mn, n·p=np, and (m·n)·p=mnp, we get m·(n·p)=mnp. *)

  let rec comp_assocr : type a m b n c d p mn np mnp.
      (a, m, b, n, c, mn) comp ->
      (b, n, c, p, d, np) comp ->
      (a, mn, c, p, d, mnp) comp ->
      (a, m, b, np, d, mnp) comp =
   fun mn np mn_p ->
    match np with
    | Zero ->
        let Zero = mn_p in
        mn
    | Suc (np_inner, edge) ->
        let (Suc (mn_p_inner, edge')) = mn_p in
        let Eq = Q.src_uniq edge edge' in
        Suc (comp_assocr mn np_inner mn_p_inner, edge)

  (* ********** Comparison ********** *)

  let rec compare : type a1 m1 b1 a2 m2 b2.
      (a1, m1, b1) t -> (a2, m2, b2) t -> (a1 * m1 * b1, a2 * m2 * b2) Eq.compare =
   fun p1 p2 ->
    match (p1, p2) with
    | Path (a1, Zero), Path (a2, Zero) -> (
        match Obj.compare a1 a2 with
        | Eq -> Eq
        | Neq -> Neq)
    | Path (_, Zero), Path (_, Suc _) -> Neq
    | Path (_, Suc _), Path (_, Zero) -> Neq
    | Path (a1, Suc (m1, g1)), Path (a2, Suc (m2, g2)) -> (
        match compare (Path (a1, m1)) (Path (a2, m2)) with
        | Neq -> Neq
        | Eq -> (
            match Q.compare g1 g2 with
            | Eq -> Eq
            | Neq -> Neq))
end
