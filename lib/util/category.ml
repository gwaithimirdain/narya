open Signatures
open Monoid

(* Module signatures for type-level categories.  At least in Util, we use "source" and "target" for morphisms in a small category, and "domain" and "codomain" for morphisms in a large category (e.g. homomorphisms of monoids, quiver maps, functors between small categories). *)

module type Quiver = sig
  module Obj : Comparable

  (* Morphisms in a quiver (or category) are parametrized by source and target. *)
  type ('src, 'morphism, 'tgt) t

  val src : ('src, 'morphism, 'tgt) t -> 'src Obj.t
  val tgt : ('src, 'morphism, 'tgt) t -> 'tgt Obj.t

  (* But a given morphism has exactly one source and target. *)
  val src_uniq : ('src1, 'morphism, 'tgt1) t -> ('src2, 'morphism, 'tgt2) t -> ('src1, 'src2) Eq.t
  val tgt_uniq : ('src1, 'morphism, 'tgt1) t -> ('src2, 'morphism, 'tgt2) t -> ('tgt1, 'tgt2) Eq.t

  val compare :
    ('d1, 'g1, 'c1) t -> ('d2, 'g2, 'c2) t -> ('d1 * 'g1 * 'c1, 'd2 * 'g2 * 'c2) Eq.compare
end

module type Quivermap = sig
  module Dom : Quiver
  module Cod : Quiver
  module Obj : Function with module Dom = Dom.Obj and module Cod = Cod.Obj

  type ('dom_src, 'dom_morphism, 'dom_tgt, 'cod_src, 'cod_morphism, 'cod_tgt) t

  val dom : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) Dom.t
  val cod : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('x, 'n, 'y) Cod.t

  (* Images of morphisms are compatible with images of their source and target. *)
  val src : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'x) Obj.t
  val tgt : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('b, 'y) Obj.t

  type (_, _, _) exists = Exists : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) exists

  val exists : ('a, 'm, 'b) Dom.t -> ('a, 'm, 'b) exists

  val uniq :
    ('a, 'm, 'b, 'x1, 'n1, 'y1) t ->
    ('a, 'm, 'b, 'x2, 'n2, 'y2) t ->
    ('x1 * 'n1 * 'y1, 'x2 * 'n2 * 'y2) Eq.t
end

module type Quivermap2 = sig
  module Param : Fam
  module Dom : Quiver
  module Cod : Quiver
  module Obj : Function2 with module Param = Param and module Dom = Dom.Obj and module Cod = Cod.Obj

  type ('param, 'dom_src, 'dom_morphism, 'dom_tgt, 'cod_src, 'cod_morphism, 'cod_tgt) t

  val dom : ('param, 'a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) Dom.t
  val cod : 'param Param.t -> ('param, 'a, 'm, 'b, 'x, 'n, 'y) t -> ('x, 'n, 'y) Cod.t

  (* Images of morphisms are compatible with images of their source and target. *)
  val src : ('param, 'a, 'm, 'b, 'x, 'n, 'y) t -> ('param, 'a, 'x) Obj.t
  val tgt : ('param, 'a, 'm, 'b, 'x, 'n, 'y) t -> ('param, 'b, 'y) Obj.t

  type (_, _, _, _) exists =
    | Exists : ('param, 'a, 'm, 'b, 'x, 'n, 'y) t -> ('param, 'a, 'm, 'b) exists

  val exists : 'param Param.t -> ('a, 'm, 'b) Dom.t -> ('param, 'a, 'm, 'b) exists

  val uniq :
    ('param, 'a, 'm, 'b, 'x1, 'n1, 'y1) t ->
    ('param, 'a, 'm, 'b, 'x2, 'n2, 'y2) t ->
    ('x1 * 'n1 * 'y1, 'x2 * 'n2 * 'y2) Eq.t
end

module type Category = sig
  include Quiver

  (* The type parameters of composition are in applicative order: ('a, 'm, 'b, 'n, 'c, 'p) comp says that 'm is a morphism from 'a to 'b, 'n is a morphism from 'b to 'c, and 'p is the composite n ∘ m from 'a to 'c. *)
  type (_, _, _, _, _, _) comp

  type (_, _, _, _, _) has_comp =
    | Comp : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b, 'n, 'c) has_comp

  (* As with Monoid, the choice of which arguments must be supplied and which can be deduced mirrors what happens in the free case.  In the free case (Path), the comp evidence is built by walking the precomposed ('m) morphism, so [comp] takes that morphism. *)
  val comp : ('a, 'm, 'b) t -> ('a, 'm, 'b, 'n, 'c) has_comp
  val comp_right : 'b Obj.t -> ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b) t
  val comp_left : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'p, 'c) t -> ('b, 'n, 'c) t
  val comp_out : ('b, 'n, 'c) t -> ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'p, 'c) t

  (* Composites are unique *)
  val comp_uniq : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b, 'n, 'c, 'q) comp -> ('p, 'q) Eq.t

  (* Identity morphisms.  This type has to be parametrized by the object so that src_uniq and tgt_uniq have a chance of being true. *)
  type 'a id

  val id : 'a Obj.t -> ('a, 'a id, 'a) t

  (* Composition is unital. *)
  val id_comp : ('a, 'm, 'b) t -> ('a, 'm, 'b, 'b id, 'b, 'm) comp
  val comp_id : ('b, 'n, 'c) t -> ('b, 'b id, 'b, 'n, 'c, 'n) comp

  (* Composition is associative. *)
  val comp_assocr :
    ('b, 'n, 'c, 'p, 'd, 'np) comp ->
    ('a, 'm, 'b, 'n, 'c, 'mn) comp ->
    ('a, 'm, 'b, 'np, 'd, 'mnp) comp ->
    ('a, 'mn, 'c, 'p, 'd, 'mnp) comp

  val comp_assocl :
    ('b, 'n, 'c, 'p, 'd, 'np) comp ->
    ('a, 'm, 'b, 'n, 'c, 'mn) comp ->
    ('a, 'mn, 'c, 'p, 'd, 'mnp) comp ->
    ('a, 'm, 'b, 'np, 'd, 'mnp) comp
end

(* A Quivermap whose domain and codomain are categories, that preserves identities and composition.  This is a functor in the category-theoretic sense. *)

module type Functor = sig
  module Dom : Category
  module Cod : Category
  include Quivermap with module Dom := Dom and module Cod := Cod

  (* The functor preserves identities. *)
  val id : ('a, 'x) Obj.t -> ('a, 'a Dom.id, 'a, 'x, 'x Cod.id, 'x) t

  (* The functor preserves composition: given the images of two composable morphisms in Dom and evidence that they compose, we get the image of the composite together with evidence that the images compose in Cod. *)

  type (_, _, _, _, _, _, _, _) comp =
    | Comp :
        ('a, 'p, 'c, 'x, 'n3, 'z) t * ('x, 'n2, 'y, 'n1, 'z, 'n3) Cod.comp
        -> ('a, 'p, 'c, 'x, 'n2, 'y, 'n1, 'z) comp

  val comp :
    ('a, 'm, 'b, 'x, 'n2, 'y) t ->
    ('b, 'n, 'c, 'y, 'n1, 'z) t ->
    ('a, 'm, 'b, 'n, 'c, 'p) Dom.comp ->
    ('a, 'p, 'c, 'x, 'n2, 'y, 'n1, 'z) comp

  (* Conversely, the image of a composite morphism factors through images of the factors. *)

  type (_, _, _, _, _, _, _, _) uncomp =
    | Uncomp :
        ('b, 'n, 'c, 'y, 'r, 'z) t * ('a, 'm, 'b, 'x, 'q, 'y) t * ('x, 'q, 'y, 'r, 'z, 'rq) Cod.comp
        -> ('a, 'm, 'b, 'n, 'c, 'x, 'rq, 'z) uncomp

  val uncomp :
    ('a, 'm, 'b, 'n, 'c, 'nm) Dom.comp ->
    ('a, 'nm, 'c, 'x, 'rq, 'z) t ->
    ('a, 'm, 'b, 'n, 'c, 'x, 'rq, 'z) uncomp
end

module OneObject (M : Monoid) = struct
  module Obj = Unitcomparable

  type (_, _, _) t = Loop : 'm M.t -> (unit, 'm, unit) t

  let src : type src m tgt. (src, m, tgt) t -> src Obj.t = fun (Loop _) -> Unit
  let tgt : type src m tgt. (src, m, tgt) t -> tgt Obj.t = fun (Loop _) -> Unit

  (* But a given morphism has exactly one source and target. *)
  let src_uniq : type src1 m tgt1 src2 tgt2.
      (src1, m, tgt1) t -> (src2, m, tgt2) t -> (src1, src2) Eq.t =
   fun (Loop _) (Loop _) -> Eq

  let tgt_uniq : type src1 m tgt1 src2 tgt2.
      (src1, m, tgt1) t -> (src2, m, tgt2) t -> (tgt1, tgt2) Eq.t =
   fun (Loop _) (Loop _) -> Eq

  let compare : type d1 g1 c1 d2 g2 c2.
      (d1, g1, c1) t -> (d2, g2, c2) t -> (d1 * g1 * c1, d2 * g2 * c2) Eq.compare =
   fun (Loop m1) (Loop m2) ->
    match M.compare m1 m2 with
    | Eq -> Eq
    | Neq -> Neq

  type (_, _, _, _, _, _) comp =
    | Loopcomp : ('n, 'm, 'nm) M.plus -> (unit, 'm, unit, 'n, 'c, 'nm) comp

  type (_, _, _, _, _) has_comp =
    | Comp : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b, 'n, 'c) has_comp

  let comp : type a m b n c. (a, m, b) t -> (a, m, b, n, c) has_comp =
   fun (Loop m) ->
    let (Plus mn) = M.plus m in
    Comp (Loopcomp mn)

  let comp_right : type a m b n c p. b Obj.t -> (a, m, b, n, c, p) comp -> (a, m, b) t =
   fun Unit (Loopcomp mn) -> Loop (M.plus_right mn)

  let comp_left : type a m b n c nm. (a, m, b, n, c, nm) comp -> (a, nm, c) t -> (b, n, c) t =
   fun (Loopcomp n_m) (Loop nm) -> Loop (M.plus_left n_m nm)

  let comp_out : type a m b n c p. (b, n, c) t -> (a, m, b, n, c, p) comp -> (a, p, c) t =
   fun (Loop n) (Loopcomp nm) -> Loop (M.plus_out n nm)

  let comp_uniq : type a m b n c p q.
      (a, m, b, n, c, p) comp -> (a, m, b, n, c, q) comp -> (p, q) Eq.t =
   fun (Loopcomp mn) (Loopcomp mn') -> M.plus_uniq mn mn'

  type 'a id = M.zero

  let id : type a. a Obj.t -> (a, a id, a) t = fun Unit -> Loop M.zero

  let id_comp : type a m b. (a, m, b) t -> (a, m, b, b id, b, m) comp =
   fun (Loop m) -> Loopcomp (M.zero_plus m)

  let comp_id : type b n c. (b, n, c) t -> (b, b id, b, n, c, n) comp =
   fun (Loop n) -> Loopcomp (M.plus_zero n)

  (* Composition is associative. *)
  let comp_assocr : type a m b n c mn p d np mnp.
      (b, n, c, p, d, np) comp ->
      (a, m, b, n, c, mn) comp ->
      (a, m, b, np, d, mnp) comp ->
      (a, mn, c, p, d, mnp) comp =
   fun (Loopcomp np) (Loopcomp mn) (Loopcomp m_np) -> Loopcomp (M.plus_assocr np mn m_np)

  let comp_assocl : type a m b n c mn p np d mnp.
      (b, n, c, p, d, np) comp ->
      (a, m, b, n, c, mn) comp ->
      (a, mn, c, p, d, mnp) comp ->
      (a, m, b, np, d, mnp) comp =
   fun (Loopcomp np) (Loopcomp mn) (Loopcomp mn_p) -> Loopcomp (M.plus_assocl np mn mn_p)
end

module ObjObjectCheck (M : Monoid) : Quiver = OneObject (M)
