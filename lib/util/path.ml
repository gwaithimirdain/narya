open Signatures
open Tbwd
open Category

(* Type-level free categories. *)

(* The free category on a quiver.  Its objects are those of the quiver, and its morphisms ("paths") are sequences of composable edges.  As with words (free monoids), paths are represented as type-level backwards lists of edges (so we can append on the right efficiently).  Composition is in applicative order: g ∘ f means f is applied first.  Appending an edge on the right of a path PRECOMPOSES that edge: the new edge is applied first, before the rest of the path.  Composition is encoded as a relation. *)

module Make (Q : Quiver) = struct
  module Obj = Q.Obj

  type 'a id = private Dummy_id
  type ('n, 'g) suc = ('n, 'g) snoc

  (* ********** Composition ********** *)

  (* ('a, 'm, 'b, 'n, 'c, 'p) comp says that a path 'm: 'a → 'b composed (as the inner / first-applied "f") with a path 'n: 'b → 'c (as the outer / second-applied "g") yields a path 'p = n ∘ m: 'a → 'c.  As with Word, we never carry around the outer path 'n explicitly inside this evidence; the outer shape and target object are existential, and the structure of the evidence mirrors the snoc-list structure of the inner path 'm. *)

  type (_, _, _, _, _, _) comp =
    | Zero : ('a, 'a id, 'a, 'n, 'c, 'n) comp
    | Suc :
        ('a1, 'm, 'b, 'n, 'c, 'p) comp * ('a, 'g, 'a1) Q.t
        -> ('a, ('m, 'g) suc, 'b, 'n, 'c, ('p, 'g) suc) comp

  (* A valid path 'morphism from 'src to 'tgt.  Following Word, this is "anything that can sit at the inner position of a composition"; we additionally remember the target object so that, e.g., the identity path can produce a source object on demand. *)

  type (_, _, _) t =
    | Path :
        ('src, 'morphism, 'tgt, 'any_n, 'any_c, 'any_p) comp * 'tgt Obj.t
        -> ('src, 'morphism, 'tgt) t

  type (_, _) wrapped = Wrap : ('src, 'morphism, 'tgt) t -> ('src, 'tgt) wrapped
  type _ src_wrapped = Wrap : ('src, 'morphism, 'tgt) t -> 'tgt src_wrapped
  type _ tgt_wrapped = Wrap : ('src, 'morphism, 'tgt) t -> 'src tgt_wrapped

  (* Smart constructors *)

  let id : type a. a Obj.t -> (a, a id, a) t = fun a -> Path (Zero, a)

  let suc : type a c b m g. (a, m, b) t -> (c, g, a) Q.t -> (c, (m, g) suc, b) t =
   fun (Path (m, b)) g -> Path (Suc (m, g), b)

  let of_gen : type a m b. (a, m, b) Q.t -> (a, (b id, m) suc, b) t =
   fun m -> Path (Suc (Zero, m), Q.tgt m)

  (* ********** Source and target ********** *)

  let src : type a m b. (a, m, b) t -> a Obj.t =
   fun (Path (p, b)) ->
    match p with
    | Zero -> b
    | Suc (_, g) -> Q.src g

  let tgt : type a m b. (a, m, b) t -> b Obj.t = fun (Path (_, b)) -> b

  let src_uniq : type src1 src2 tgt1 tgt2 morphism.
      (src1, morphism, tgt1) t -> (src2, morphism, tgt2) t -> (src1, src2) Eq.t =
   fun m1 m2 ->
    match (m1, m2) with
    | Path (Zero, _), Path (Zero, _) -> Eq
    | Path (Suc (_, g1), _), Path (Suc (_, g2), _) -> Q.src_uniq g1 g2

  let rec tgt_uniq : type src1 src2 tgt1 tgt2 morphism.
      (src1, morphism, tgt1) t -> (src2, morphism, tgt2) t -> (tgt1, tgt2) Eq.t =
   fun m1 m2 ->
    match (m1, m2) with
    | Path (Zero, _), Path (Zero, _) -> Eq
    | Path (Suc (m1_inner, _), b1), Path (Suc (m2_inner, _), b2) ->
        tgt_uniq (Path (m1_inner, b1)) (Path (m2_inner, b2))

  (* ********** Computing compositions ********** *)

  type (_, _, _, _, _) has_comp =
    | Comp : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b, 'n, 'c) has_comp

  (* [comp m] takes the inner ("f") path and proves it can be composed with any outer path. *)
  let rec comp : type a m b n c. (a, m, b) t -> (a, m, b, n, c) has_comp = function
    | Path (Zero, _) -> Comp Zero
    | Path (Suc (m, g), b) ->
        let (Comp mn) = comp (Path (m, b)) in
        Comp (Suc (mn, g))

  (* [comp_out n ev]: given the outer path n and comp evidence with m at position 'm', compute the composite path p. *)
  let rec comp_out : type a m b n c p. (b, n, c) t -> (a, m, b, n, c, p) comp -> (a, p, c) t =
   fun n ev ->
    match ev with
    | Zero -> n
    | Suc (ev_inner, g) ->
        let p_inner = comp_out n ev_inner in
        suc p_inner g

  let comp_right : type a m b n c p. b Obj.t -> (a, m, b, n, c, p) comp -> (a, m, b) t =
   fun b ev -> Path (ev, b)

  let rec comp_left : type a m b n c p. (a, m, b, n, c, p) comp -> (a, p, c) t -> (b, n, c) t =
   fun ev result ->
    match (ev, result) with
    | Zero, _ -> result
    | Suc (ev_inner, edge), Path (Suc (inner, edge'), c_obj) ->
        let Eq = Q.tgt_uniq edge edge' in
        comp_left ev_inner (Path (inner, c_obj))

  let rec comp_uniq : type a m b n c p p'.
      (a, m, b, n, c, p) comp -> (a, m, b, n, c, p') comp -> (p, p') Eq.t =
   fun mn mn' ->
    match (mn, mn') with
    | Zero, Zero -> Eq
    | Suc (mn, edge), Suc (mn', edge') ->
        let Eq = Q.tgt_uniq edge edge' in
        let Eq = comp_uniq mn mn' in
        Eq

  (* ********** Unitality ********** *)

  (* [id_comp m]: identity is on the OUTER (g) side: comp id_b m = m.  Built by walking m's structure. *)
  let rec id_comp : type a m b. (a, m, b) t -> (a, m, b, b id, b, m) comp =
   fun (Path (ev, b_obj)) ->
    match ev with
    | Zero -> Zero
    | Suc (m_inner, g) -> Suc (id_comp (Path (m_inner, b_obj)), g)

  (* [comp_id n]: identity is on the INNER (f) side: comp n id_b = n.  Direct from Zero. *)
  let comp_id : type b n c. (b, n, c) t -> (b, b id, b, n, c, n) comp = fun _ -> Zero

  (* ********** Associativity ********** *)

  (* In applicative reading: given evidence n∘m=mn, p∘n=np, and (p∘n)∘m=mnp (left-assoc input), derive p∘(n∘m)=mnp (right-assoc output).  The implementation walks m. *)

  let rec comp_assocr : type a m b n c d p mn np mnp.
      (b, n, c, p, d, np) comp ->
      (a, m, b, n, c, mn) comp ->
      (a, m, b, np, d, mnp) comp ->
      (a, mn, c, p, d, mnp) comp =
   fun np mn mn_p ->
    match mn with
    | Zero ->
        let Zero = mn_p in
        np
    | Suc (mn_inner, edge) ->
        let (Suc (mn_p_inner, edge')) = mn_p in
        let Eq = Q.tgt_uniq edge edge' in
        Suc (comp_assocr np mn_inner mn_p_inner, edge)

  (* Reverse direction: from p∘(n∘m)=mnp (right-assoc input), derive (p∘n)∘m=mnp (left-assoc output). *)

  let rec comp_assocl : type a m b n c d p mn np mnp.
      (b, n, c, p, d, np) comp ->
      (a, m, b, n, c, mn) comp ->
      (a, mn, c, p, d, mnp) comp ->
      (a, m, b, np, d, mnp) comp =
   fun np mn mnp ->
    match mn with
    | Zero ->
        let Eq = comp_uniq np mnp in
        Zero
    | Suc (mn_inner, edge) ->
        let (Suc (mnp_inner, edge')) = mnp in
        let Eq = Q.tgt_uniq edge edge' in
        Suc (comp_assocl np mn_inner mnp_inner, edge)

  (* ********** Comparison ********** *)

  let rec compare : type a1 m1 b1 a2 m2 b2.
      (a1, m1, b1) t -> (a2, m2, b2) t -> (a1 * m1 * b1, a2 * m2 * b2) Eq.compare =
   fun p1 p2 ->
    match (p1, p2) with
    | Path (Zero, b1), Path (Zero, b2) -> (
        match Obj.compare b1 b2 with
        | Eq -> Eq
        | Neq -> Neq)
    | Path (Zero, _), Path (Suc _, _) -> Neq
    | Path (Suc _, _), Path (Zero, _) -> Neq
    | Path (Suc (m1, g1), b1), Path (Suc (m2, g2), b2) -> (
        match compare (Path (m1, b1)) (Path (m2, b2)) with
        | Neq -> Neq
        | Eq -> (
            match Q.compare g1 g2 with
            | Eq -> Eq
            | Neq -> Neq))

  (* ********** Factoring and pushouts ********** *)

  (* TODO *)
end

module MakeCheck (Q : Quiver) : Category = Make (Q)

(* Functors out of a free category, determined by a map on the generating quiver.  Analogous to Word.Hom: given a quiver Q, a target category Cod, and a quiver morphism F sending objects of Q to objects of Cod and edges of Q to morphisms (paths) of Cod, this defines the unique functor Path.Make(Q) -> Cod that extends F. *)

module Hom (Q : Quiver) (Cod : Category) (F : Quivermap with module Dom = Q and module Cod = Cod) =
struct
  module Dom = Make (Q)
  module Cod = Cod
  module Obj = F.Obj

  (* ('a, 'm, 'b, 'x, 'n, 'y) t says that the path 'a -> 'b of shape 'm in Dom is sent to the morphism 'x -> 'y of shape 'n in Cod.  In applicative reading: the rightmost edge of m is the FIRST applied; its image is the inner of a Cod composition with the image of the rest of m as the outer. *)

  type (_, _, _, _, _, _) t =
    | Zero : ('a, 'x) F.Obj.t -> ('a, 'a Dom.id, 'a, 'x, 'x Cod.id, 'x) t
    | Suc :
        ('a1, 'm, 'b, 'x1, 'n1, 'y) t
        * ('a, 'g, 'a1, 'x, 'n2, 'x1) F.t
        * ('x, 'n2, 'x1, 'n1, 'y, 'n3) Cod.comp
        -> ('a, ('m, 'g) Dom.suc, 'b, 'x, 'n3, 'y) t

  let rec dom : type a m b x n y. (a, m, b, x, n, y) t -> (a, m, b) Dom.t = function
    | Zero fab -> Dom.id (F.Obj.dom fab)
    | Suc (fm, fg, _) -> Dom.suc (dom fm) (F.dom fg)

  let rec cod : type a m b x n y. (a, m, b, x, n, y) t -> (x, n, y) Cod.t = function
    | Zero fab -> Cod.id (F.Obj.cod fab)
    | Suc (fm, _, n12) -> Cod.comp_out (cod fm) n12

  (* The object-map witnesses for the source and target of a homomorphism. *)

  let src : type a m b x n y. (a, m, b, x, n, y) t -> (a, x) F.Obj.t = function
    | Zero fab -> fab
    | Suc (_, fg, _) -> F.src fg

  let rec tgt : type a m b x n y. (a, m, b, x, n, y) t -> (b, y) F.Obj.t = function
    | Zero fab -> fab
    | Suc (fm, _, _) -> tgt fm

  type (_, _, _) exists = Exists : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) exists

  let rec exists : type a m b. (a, m, b) Dom.t -> (a, m, b) exists =
   fun path ->
    match path with
    | Path (Zero, b_obj) ->
        let (Exists fab) = F.Obj.exists b_obj in
        Exists (Zero fab)
    | Path (Suc (m_inner, g_edge), b_obj) ->
        let (Exists fm) = exists (Path (m_inner, b_obj)) in
        let (Exists fg) = F.exists g_edge in
        let Eq = F.Obj.uniq (F.tgt fg) (src fm) in
        let (Comp n12) = Cod.comp (F.cod fg) in
        Exists (Suc (fm, fg, n12))

  let rec uniq : type a m b x1 n1 y1 x2 n2 y2.
      (a, m, b, x1, n1, y1) t -> (a, m, b, x2, n2, y2) t -> (x1 * n1 * y1, x2 * n2 * y2) Eq.t =
   fun f1 f2 ->
    match (f1, f2) with
    | Zero fab1, Zero fab2 ->
        let Eq = F.Obj.uniq fab1 fab2 in
        Eq
    | Suc (m1, g1, n1), Suc (m2, g2, n2) ->
        let Eq = Q.tgt_uniq (F.dom g1) (F.dom g2) in
        let Eq = uniq m1 m2 in
        let Eq = F.uniq g1 g2 in
        let Eq = Cod.comp_uniq n1 n2 in
        Eq

  (* The functor preserves identities *)

  let id : type a x. (a, x) F.Obj.t -> (a, a Dom.id, a, x, x Cod.id, x) t = fun fa -> Zero fa

  (* The functor preserves composition: given homomorphism evidence for two composable paths (fa for the outer/g, fb for the inner/f) and evidence that they compose in Dom, we obtain homomorphism evidence for the composite path together with evidence that the images compose in Cod. *)

  type (_, _, _, _, _, _, _, _) comp =
    | Comp :
        ('a, 'p, 'c, 'x, 'n3, 'z) t * ('x, 'n2, 'y, 'n1, 'z, 'n3) Cod.comp
        -> ('a, 'p, 'c, 'x, 'n2, 'y, 'n1, 'z) comp

  (* Dom.comp evidence: (a, m, b, n, c, p) Dom.comp where m is inner (a→b), n is outer (b→c), p = n∘m.
     We have fm: (a, m, b, x, n2, y) Hom (image of m is n2: x→y), and fn: (b, n, c, y, n1, z) Hom (image of n is n1: y→z).  We want to construct Hom evidence for the composite p: a→c, with image n3 = n1 ∘ n2: x→z.  Walk the m structure (the inner of Dom.comp). *)

  let rec comp : type a m b n c p x y z n1 n2.
      (a, m, b, x, n2, y) t ->
      (b, n, c, y, n1, z) t ->
      (a, m, b, n, c, p) Dom.comp ->
      (a, p, c, x, n2, y, n1, z) comp =
   fun fm fn mn ->
    match (fm, mn) with
    | Zero _, Zero -> Comp (fn, Cod.comp_id (cod fn))
    | Suc (fm_inner, fg, x_fg), Suc (mn_inner, edge) ->
        let Eq = Q.tgt_uniq (F.dom fg) edge in
        let (Comp (fp_inner, x_yfg)) = comp fm_inner fn mn_inner in
        let (Comp xfg_y) = Cod.comp (F.cod fg) in
        let x_y = Cod.comp_assocr x_yfg x_fg xfg_y in
        Comp (Suc (fp_inner, fg, xfg_y), x_y)

  (* If instead we know the image of a composite path, we can extract the images of the factors, which compose to the image of the composite.  This would be just taking the images of the factors and then using uniqueness, except that we aren't passed witnesses of the validity of those factors but rather extract them from the witness to the image of the composite. *)

  type (_, _, _, _, _, _, _, _) uncomp =
    | Uncomp :
        ('b, 'n, 'c, 'y, 'r, 'z) t * ('a, 'm, 'b, 'x, 'q, 'y) t * ('x, 'q, 'y, 'r, 'z, 'rq) Cod.comp
        -> ('a, 'm, 'b, 'n, 'c, 'x, 'rq, 'z) uncomp

  let rec uncomp : type a m b n c nm x z rq.
      (a, m, b, n, c, nm) Dom.comp -> (a, nm, c, x, rq, z) t -> (a, m, b, n, c, x, rq, z) uncomp =
   fun nm fnm ->
    match nm with
    | Zero -> Uncomp (fnm, Zero (src fnm), Cod.comp_id (cod fnm))
    | Suc (nm, g) ->
        let (Suc (fnm, fg, rq_h)) = fnm in
        let Eq = Q.tgt_uniq g (F.dom fg) in
        let (Uncomp (fn, fm, rq)) = uncomp nm fnm in
        let h = F.cod fg in
        let (Comp qh) = Cod.comp h in
        let r_qh = Cod.comp_assocr rq qh rq_h in
        let f_mg = Suc (fm, fg, qh) in
        Uncomp (fn, f_mg, r_qh)
end

module HomCheck
    (Q : Quiver)
    (Cod : Category)
    (F : Quivermap with module Dom = Q and module Cod = Cod) :
  Quivermap with module Dom = Make(Q) and module Cod = Cod =
  Hom (Q) (Cod) (F)

(* Parametrized families of functors *)

module Hom2
    (Param : Fam)
    (Q : Quiver)
    (Cod : Category)
    (F : Quivermap2 with module Param = Param and module Dom = Q and module Cod = Cod) =
struct
  module Param = Param
  module Dom = Make (Q)
  module Cod = Cod
  module Obj = F.Obj

  type (_, _, _, _, _, _, _) t =
    | Zero : ('param, 'a, 'x) F.Obj.t -> ('param, 'a, 'a Dom.id, 'a, 'x, 'x Cod.id, 'x) t
    | Suc :
        ('param, 'a1, 'm, 'b, 'x1, 'n1, 'y) t
        * ('param, 'a, 'g, 'a1, 'x, 'n2, 'x1) F.t
        * ('x, 'n2, 'x1, 'n1, 'y, 'n3) Cod.comp
        -> ('param, 'a, ('m, 'g) Dom.suc, 'b, 'x, 'n3, 'y) t

  let rec dom : type param a m b x n y. (param, a, m, b, x, n, y) t -> (a, m, b) Dom.t = function
    | Zero fab -> Dom.id (F.Obj.dom fab)
    | Suc (fm, fg, _) -> Dom.suc (dom fm) (F.dom fg)

  let rec cod : type param a m b x n y.
      param Param.t -> (param, a, m, b, x, n, y) t -> (x, n, y) Cod.t =
   fun param -> function
    | Zero fab -> Cod.id (F.Obj.cod param fab)
    | Suc (fm, _, n12) -> Cod.comp_out (cod param fm) n12

  let src : type param a m b x n y. (param, a, m, b, x, n, y) t -> (param, a, x) F.Obj.t = function
    | Zero fab -> fab
    | Suc (_, fg, _) -> F.src fg

  let rec tgt : type param a m b x n y. (param, a, m, b, x, n, y) t -> (param, b, y) F.Obj.t =
    function
    | Zero fab -> fab
    | Suc (fm, _, _) -> tgt fm

  type (_, _, _, _) exists =
    | Exists : ('param, 'a, 'm, 'b, 'x, 'n, 'y) t -> ('param, 'a, 'm, 'b) exists

  let rec exists : type param a m b. param Param.t -> (a, m, b) Dom.t -> (param, a, m, b) exists =
   fun param path ->
    match path with
    | Path (Zero, b_obj) ->
        let (Exists fab) = F.Obj.exists param b_obj in
        Exists (Zero fab)
    | Path (Suc (m_inner, g_edge), b_obj) ->
        let (Exists fm) = exists param (Path (m_inner, b_obj)) in
        let (Exists fg) = F.exists param g_edge in
        let Eq = F.Obj.uniq (F.tgt fg) (src fm) in
        let (Comp n12) = Cod.comp (F.cod param fg) in
        Exists (Suc (fm, fg, n12))

  let rec uniq : type param a m b x1 n1 y1 x2 n2 y2.
      (param, a, m, b, x1, n1, y1) t ->
      (param, a, m, b, x2, n2, y2) t ->
      (x1 * n1 * y1, x2 * n2 * y2) Eq.t =
   fun f1 f2 ->
    match (f1, f2) with
    | Zero fab1, Zero fab2 ->
        let Eq = F.Obj.uniq fab1 fab2 in
        Eq
    | Suc (m1, g1, n1), Suc (m2, g2, n2) ->
        let Eq = Q.tgt_uniq (F.dom g1) (F.dom g2) in
        let Eq = uniq m1 m2 in
        let Eq = F.uniq g1 g2 in
        let Eq = Cod.comp_uniq n1 n2 in
        Eq

  let id : type param a x. (param, a, x) F.Obj.t -> (param, a, a Dom.id, a, x, x Cod.id, x) t =
   fun fa -> Zero fa

  type (_, _, _, _, _, _, _, _, _) comp =
    | Comp :
        ('param, 'a, 'p, 'c, 'x, 'n3, 'z) t * ('x, 'n2, 'y, 'n1, 'z, 'n3) Cod.comp
        -> ('param, 'a, 'p, 'c, 'x, 'n2, 'y, 'n1, 'z) comp

  let rec comp : type param a m b n c p x y z n1 n2.
      param Param.t ->
      (param, b, n, c, y, n1, z) t ->
      (param, a, m, b, x, n2, y) t ->
      (a, m, b, n, c, p) Dom.comp ->
      (param, a, p, c, x, n2, y, n1, z) comp =
   fun param fn fm mn ->
    match (fm, mn) with
    | Zero _, Zero -> Comp (fn, Cod.comp_id (cod param fn))
    | Suc (fm_inner, fg, x_fg), Suc (mn_inner, edge) ->
        let Eq = Q.tgt_uniq (F.dom fg) edge in
        let (Comp (fp_inner, x_yfg)) = comp param fn fm_inner mn_inner in
        let (Comp xfg_y) = Cod.comp (F.cod param fg) in
        let x_y = Cod.comp_assocr x_yfg x_fg xfg_y in
        Comp (Suc (fp_inner, fg, xfg_y), x_y)

  type (_, _, _, _, _, _, _, _, _) uncomp =
    | Uncomp :
        ('param, 'b, 'n, 'c, 'y, 'r, 'z) t
        * ('param, 'a, 'm, 'b, 'x, 'q, 'y) t
        * ('x, 'q, 'y, 'r, 'z, 'rq) Cod.comp
        -> ('param, 'a, 'm, 'b, 'n, 'c, 'x, 'rq, 'z) uncomp

  let rec uncomp : type param a m b n c nm x z rq.
      param Param.t ->
      (a, m, b, n, c, nm) Dom.comp ->
      (param, a, nm, c, x, rq, z) t ->
      (param, a, m, b, n, c, x, rq, z) uncomp =
   fun param nm fnm ->
    match nm with
    | Zero -> Uncomp (fnm, Zero (src fnm), Cod.comp_id (cod param fnm))
    | Suc (nm, g) ->
        let (Suc (fnm, fg, rq_h)) = fnm in
        let Eq = Q.tgt_uniq g (F.dom fg) in
        let (Uncomp (fn, fm, rq)) = uncomp param nm fnm in
        let h = F.cod param fg in
        let (Comp qh) = Cod.comp h in
        let r_qh = Cod.comp_assocr rq qh rq_h in
        let f_mg = Suc (fm, fg, qh) in
        Uncomp (fn, f_mg, r_qh)
end

module Hom2Check
    (Param : Fam)
    (Q : Quiver)
    (Cod : Category)
    (F : Quivermap2 with module Param = Param and module Dom = Q and module Cod = Cod) :
  Quivermap2 with module Param = Param and module Dom = Make(Q) and module Cod = Cod =
  Hom2 (Param) (Q) (Cod) (F)
