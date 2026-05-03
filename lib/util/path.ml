open Signatures
open Tbwd
open Category

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

module MakeCheck (Q : Quiver) : Category = Make (Q)

(* Functors out of a free category, determined by a map on the generating quiver.  Analogous to Word.Hom: given a quiver Q, a target category Cod, and a quiver morphism F sending objects of Q to objects of Cod and edges of Q to morphisms (paths) of Cod, this defines the unique functor Path.Make(Q) -> Cod that extends F. *)

module Hom
    (Q : Quiver)
    (Cod : Category)
    (F : sig
      module Obj : Function with module Dom = Q.Obj and module Cod = Cod.Obj

      type (_, _, _, _, _, _) t

      val dom : ('a, 'g, 'b, 'x, 'n, 'y) t -> ('a, 'g, 'b) Q.t
      val cod : ('a, 'g, 'b, 'x, 'n, 'y) t -> ('x, 'n, 'y) Cod.t
      val src : ('a, 'g, 'b, 'x, 'n, 'y) t -> ('a, 'x) Obj.t
      val tgt : ('a, 'g, 'b, 'x, 'n, 'y) t -> ('b, 'y) Obj.t

      type (_, _, _) exists = Exists : ('a, 'g, 'b, 'x, 'n, 'y) t -> ('a, 'g, 'b) exists

      val exists : ('a, 'g, 'b) Q.t -> ('a, 'g, 'b) exists

      val uniq :
        ('a, 'g, 'b, 'x1, 'n1, 'y1) t ->
        ('a, 'g, 'b, 'x2, 'n2, 'y2) t ->
        ('x1 * 'n1 * 'y1, 'x2 * 'n2 * 'y2) Eq.t
    end) =
struct
  module Dom = Make (Q)
  module Cod = Cod

  (* ('a, 'm, 'b, 'x, 'n, 'y) t says that the path 'a -> 'b of shape 'm in Dom is sent to the morphism 'x -> 'y of shape 'n in Cod.  The Zero constructor remembers an object-map witness so we can reconstruct the (identity) image from it. *)

  type (_, _, _, _, _, _) t =
    | Zero : ('a, 'x) F.Obj.t -> ('a, Dom.zero, 'a, 'x, Cod.zero, 'x) t
    | Suc :
        ('a, 'm, 'b, 'x, 'n1, 'y) t
        * ('b, 'g, 'c, 'y, 'n2, 'z) F.t
        * ('x, 'n1, 'y, 'n2, 'z, 'n3) Cod.comp
        -> ('a, ('m, 'g) Dom.suc, 'c, 'x, 'n3, 'z) t

  let rec dom : type a m b x n y. (a, m, b, x, n, y) t -> (a, m, b) Dom.t = function
    | Zero fab -> Dom.id (F.Obj.dom fab)
    | Suc (fm, fg, _) -> Dom.suc (dom fm) (F.dom fg)

  let rec cod : type a m b x n y. (a, m, b, x, n, y) t -> (x, n, y) Cod.t = function
    | Zero fab -> Cod.id (F.Obj.cod fab)
    | Suc (fm, _, n12) -> Cod.comp_out (cod fm) n12

  (* The object-map witnesses for the source and target of a homomorphism. *)

  let rec src_obj : type a m b x n y. (a, m, b, x, n, y) t -> (a, x) F.Obj.t = function
    | Zero fab -> fab
    | Suc (fm, _, _) -> src_obj fm

  let tgt_obj : type a m b x n y. (a, m, b, x, n, y) t -> (b, y) F.Obj.t = function
    | Zero fab -> fab
    | Suc (_, fg, _) -> F.tgt fg

  type (_, _, _) exists = Exists : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) exists

  let rec exists : type a m b. (a, m, b) Dom.t -> (a, m, b) exists =
   fun path ->
    match path with
    | Path (a, Zero) ->
        let (Exists fab) = F.Obj.exists a in
        Exists (Zero fab)
    | Path (a, Suc (m_inner, g_edge)) ->
        let (Exists fm) = exists (Path (a, m_inner)) in
        let (Exists fg) = F.exists g_edge in
        let Eq = F.Obj.uniq (tgt_obj fm) (F.src fg) in
        let (Comp n12) = Cod.comp (F.cod fg) in
        Exists (Suc (fm, fg, n12))

  let rec uniq : type a m b x1 n1 y1 x2 n2 y2.
      (a, m, b, x1, n1, y1) t ->
      (a, m, b, x2, n2, y2) t ->
      (x1 * n1 * y1, x2 * n2 * y2) Eq.t =
   fun f1 f2 ->
    match (f1, f2) with
    | Zero fab1, Zero fab2 ->
        let Eq = F.Obj.uniq fab1 fab2 in
        Eq
    | Suc (m1, g1, n1), Suc (m2, g2, n2) ->
        let Eq = Q.src_uniq (F.dom g1) (F.dom g2) in
        let Eq = uniq m1 m2 in
        let Eq = F.uniq g1 g2 in
        let Eq = Cod.comp_uniq n1 n2 in
        Eq

  (* The functor preserves composition: given homomorphism evidence for two composable paths and evidence that they compose in Dom, we obtain homomorphism evidence for the composite path together with evidence that the images compose in Cod. *)

  type (_, _, _, _, _, _, _, _) comp =
    | Comp :
        ('a, 'p, 'c, 'x, 'n3, 'z) t * ('x, 'n1, 'y, 'n2, 'z, 'n3) Cod.comp
        -> ('a, 'p, 'c, 'x, 'n1, 'y, 'n2, 'z) comp

  let rec comp : type a m b n c p x y z n1 n2.
      (a, m, b, x, n1, y) t ->
      (b, n, c, y, n2, z) t ->
      (a, m, b, n, c, p) Dom.comp ->
      (a, p, c, x, n1, y, n2, z) comp =
   fun fa fb ab ->
    match (fb, ab) with
    | Zero _, Zero -> Comp (fa, Cod.comp_id (cod fa))
    | Suc (fb_inner, fg, y_fg), Suc (ab_inner, edge) ->
        let Eq = Q.src_uniq (F.dom fg) edge in
        let (Comp (fc, xy)) = comp fa fb_inner ab_inner in
        let (Comp xy_fg) = Cod.comp (F.cod fg) in
        let x_yfg = Cod.comp_assocr xy y_fg xy_fg in
        Comp (Suc (fc, fg, xy_fg), x_yfg)
end
