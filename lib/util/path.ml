open Signatures
open Tlist
open Tbwd
open Category

(* Type-level free categories. *)

(* The free category on a quiver.  Its objects are those of the quiver, and its morphisms ("paths") are sequences of composable edges.  As with words (free monoids), paths are represented as type-level backwards lists of edges (so we can append on the right efficiently).  Composition is in applicative order: g ∘ f means f is applied first.  Appending an edge on the right of a path PRECOMPOSES that edge: the new edge is applied first, before the rest of the path.  Composition is encoded as a relation. *)
type 'a id = private Dummy_id

module Make (Q : Quiver) = struct
  module Obj = Q.Obj

  type nonrec 'a id = 'a id
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
  type (_, _) has_src = Wrap : ('src, 'morphism, 'tgt) t -> ('morphism, 'tgt) has_src
  type (_, _) has_tgt = Wrap : ('src, 'morphism, 'tgt) t -> ('src, 'morphism) has_tgt

  (* Smart constructors *)

  let id : type a. a Obj.t -> (a, a id, a) t = fun a -> Path (Zero, a)

  let suc : type a c b m g. (a, m, b) t -> (c, g, a) Q.t -> (c, (m, g) suc, b) t =
   fun (Path (m, b)) g -> Path (Suc (m, g), b)

  let of_gen : type a m b. (a, m, b) Q.t -> (a, (b id, m) suc, b) t =
   fun m -> Path (Suc (Zero, m), Q.tgt m)

  let rec length : type a m b. (a, m, b) t -> int = function
    | Path (Zero, _) -> 0
    | Path (Suc (m, _), mode) -> 1 + length (Path (m, mode))

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

  let rec comp_assoc_cancelr : type a m b n c d p nm pn pnm.
      (a, m, b, n, c, nm) comp ->
      (a, nm, c, p, d, pnm) comp ->
      (a, m, b, pn, d, pnm) comp ->
      (b, n, c, p, d, pn) comp =
   fun nm p_nm pn_m ->
    match (nm, pn_m) with
    | Zero, Zero -> p_nm
    | Suc (nm, g), Suc (pn_m, g') ->
        let Eq = Q.tgt_uniq g g' in
        let (Suc (p_nm, g'')) = p_nm in
        let Eq = Q.tgt_uniq g g'' in
        comp_assoc_cancelr nm p_nm pn_m

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

  (* ********** Forward version ********** *)

  (* Forward chain of composable edges from 'src to 'tgt, with cons head being the target-side edge.  Walking head-to-tail thus traverses the path target-to-source. *)
  type (_, _, _) fwd =
    | Nil : ('a, 'a id, 'a) fwd
    | Cons : ('mid, 'g, 'tgt) Q.t * ('src, 'rest, 'mid) fwd -> ('src, ('g, 'rest) cons, 'tgt) fwd

  let fwd_tgt_uniq : type a1 a2 m b1 b2. (a1, m, b1) fwd -> (a2, m, b2) fwd -> (b1, b2) Eq.t =
   fun m1 m2 ->
    match (m1, m2) with
    | Nil, Nil -> Eq
    | Cons (g1, _), Cons (g2, _) -> Q.tgt_uniq g1 g2

  type (_, _, _, _, _, _) bcomp =
    | Zero : ('a, 'a id, 'a, 'n, 'c, 'n) bcomp
    | Suc :
        ('b1, 'g, 'b) Q.t * ('a, 'm, 'b1, ('n, 'g) suc, 'c, 'p) bcomp
        -> ('a, ('g, 'm) cons, 'b, 'n, 'c, 'p) bcomp

  let rec bcomp_right : type x m y n z nm. (x, m, y, n, z, nm) bcomp -> (x, m, y) fwd = function
    | Zero -> Nil
    | Suc (g, nm) -> Cons (g, bcomp_right nm)

  let rec bcomp_uniq : type x m y n z nm nm'.
      (x, m, y, n, z, nm) bcomp -> (x, m, y, n, z, nm') bcomp -> (nm, nm') Eq.t =
   fun nm1 nm2 ->
    match (nm1, nm2) with
    | Zero, Zero -> Eq
    | Suc (g1, nm1), Suc (g2, nm2) ->
        let Eq = Q.src_uniq g1 g2 in
        let Eq = bcomp_uniq nm1 nm2 in
        Eq

  (* TODO: Do we need the "fwd" return value here?  It can be recovered from the "bcomp" with bcomp_right if necessary, and we don't seem to use it often. *)
  type (_, _, _) to_fwd =
    | To_fwd :
        ('src, 'fwd_shape, 'tgt) fwd * ('src, 'fwd_shape, 'tgt, 'tgt id, 'tgt, 'm) bcomp
        -> ('src, 'm, 'tgt) to_fwd

  let to_fwd : type src m tgt. (src, m, tgt) t -> (src, m, tgt) to_fwd =
   fun path ->
    let rec go : type cur m_rem src fwd_shape m_full tgt.
        (cur, m_rem, tgt) t ->
        (src, fwd_shape, cur) fwd ->
        (src, fwd_shape, cur, m_rem, tgt, m_full) bcomp ->
        (src, m_full, tgt) to_fwd =
     fun path fwd_acc bcomp_acc ->
      match path with
      | Path (Zero, _) -> To_fwd (fwd_acc, bcomp_acc)
      | Path (Suc (m_inner, g_edge), b_obj) ->
          go (Path (m_inner, b_obj)) (Cons (g_edge, fwd_acc)) (Suc (g_edge, bcomp_acc)) in
    go path Nil Zero

  type (_, _, _, _, _) has_bcomp =
    | Bcomp : ('a, 'm, 'b, 'n, 'c, 'p) bcomp -> ('a, 'm, 'b, 'n, 'c) has_bcomp

  let rec bcomp : type a m b n c. (a, m, b) fwd -> (a, m, b, n, c) has_bcomp = function
    | Nil -> Bcomp Zero
    | Cons (g, x) ->
        let (Bcomp y) = bcomp x in
        Bcomp (Suc (g, y))

  (* ********** Factoring and pushouts ********** *)

  type (_, _, _, _, _) factor =
    | Factor : ('b, 'n, 'c) t * ('a, 'k, 'b, 'n, 'c, 'nk) comp -> ('a, 'b, 'c, 'nk, 'k) factor

  let rec factor : type a b c nk k. (a, nk, c) t -> (a, k, b) t -> (a, b, c, nk, k) factor option =
   fun nk k ->
    let open Monad.Ops (Monad.Maybe) in
    match (nk, k) with
    | _, Path (Zero, _) -> Some (Factor (nk, comp_id nk))
    | Path (Suc (nk, g), base), Path (Suc (k, h), base') -> (
        match Q.compare g h with
        | Eq ->
            let* (Factor (j, n)) = factor (Path (nk, base)) (Path (k, base')) in
            return (Factor (j, Suc (n, g)))
        | Neq -> None)
    | _ -> None

  type (_, _, _, _, _) pushout =
    | Pushout :
        ('y, 'c, 'w) t
        * ('z, 'd, 'w) t
        * ('x, 'a, 'y, 'c, 'w, 'p) comp
        * ('x, 'b, 'z, 'd, 'w, 'p) comp
        -> ('x, 'y, 'z, 'a, 'b) pushout

  let pushout : type x y z a b. (x, a, y) t -> (x, b, z) t -> (x, y, z, a, b) pushout option =
   fun a b ->
    match (factor a b, factor b a) with
    | _, Some (Factor (k, ab)) -> Some (Pushout (k, id (tgt k), ab, id_comp b))
    | Some (Factor (k, ba)), _ -> Some (Pushout (id (tgt k), k, id_comp a, ba))
    | _ -> None
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
  Functor with module Dom = Make(Q) and module Cod = Cod =
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

(* (Parametrized) functoriality is the functor between two free categories induced by a map of their generating quivers, composed with the inclusion of generators into a free category. *)

module Fmap
    (Dom : Quiver)
    (Cod : Quiver)
    (F : Quivermap2 with module Dom = Dom and module Cod = Cod) =
struct
  module CodCategory = Make (Cod)
  module C = Cod

  module FCategory = struct
    module Param = F.Param
    module Dom = Dom
    module Cod = CodCategory
    module Obj = F.Obj

    type (_, _, _, _, _, _, _) t =
      | Inject :
          ('p, 'a, 'g, 'b, 'x, 'n, 'y) F.t
          -> ('p, 'a, 'g, 'b, 'x, ('y CodCategory.id, 'n) CodCategory.suc, 'y) t

    let dom : type p a g b x n y. (p, a, g, b, x, n, y) t -> (a, g, b) Dom.t =
     fun (Inject f) -> F.dom f

    let cod : type p a g b x n y. p Param.t -> (p, a, g, b, x, n, y) t -> (x, n, y) Cod.t =
     fun p (Inject f) -> CodCategory.of_gen (F.cod p f)

    let src : type p a g b x n y. (p, a, g, b, x, n, y) t -> (p, a, x) Obj.t =
     fun (Inject f) -> F.src f

    let tgt : type p a g b x n y. (p, a, g, b, x, n, y) t -> (p, b, y) Obj.t =
     fun (Inject f) -> F.tgt f

    type (_, _, _, _) exists = Exists : ('p, 'a, 'g, 'b, 'x, 'n, 'y) t -> ('p, 'a, 'g, 'b) exists

    let exists : type p a g b. p Param.t -> (a, g, b) Dom.t -> (p, a, g, b) exists =
     fun p path ->
      let (Exists fx) = F.exists p path in
      Exists (Inject fx)

    let uniq : type p a g b x1 n1 y1 x2 n2 y2.
        (p, a, g, b, x1, n1, y1) t ->
        (p, a, g, b, x2, n2, y2) t ->
        (x1 * n1 * y1, x2 * n2 * y2) Eq.t =
     fun f1 f2 ->
      match (f1, f2) with
      | Inject f1, Inject f2 ->
          let Eq = F.uniq f1 f2 in
          Eq
  end

  include Hom2 (F.Param) (Dom) (CodCategory) (FCategory)

  (* Free functors not only preserve composition but reflect it: if the image of a domain morphism factors as a composite in the codomain, then there is a unique corresponding factorization in the domain whose factors map to the given codomain factors.  These are the duals of Hom2.comp and Hom2.uncomp: those take dom composition evidence and produce cod composition evidence; these take cod composition evidence and produce dom composition evidence. *)

  type (_, _, _, _, _, _, _, _, _) dom_comp =
    | Dom_comp :
        ('param, 'a, 'p, 'c, 'x, 'n3, 'z) t * ('a, 'm, 'b, 'n, 'c, 'p) Dom.comp
        -> ('param, 'a, 'm, 'b, 'n, 'c, 'x, 'n3, 'z) dom_comp

  let rec dom_comp : type param a m b n c x y z n1 n2 n3.
      param Param.t ->
      (param, b, n, c, y, n1, z) t ->
      (param, a, m, b, x, n2, y) t ->
      (x, n2, y, n1, z, n3) Cod.comp ->
      (param, a, m, b, n, c, x, n3, z) dom_comp =
   fun param fn fm cev ->
    match (fm, cev) with
    | Zero _, Zero -> Dom_comp (fn, Zero)
    | Suc (fm_inner, Inject fg, Suc (Zero, edge_fg)), Suc (cev_inner, edge_cev) ->
        let Eq = C.tgt_uniq edge_fg edge_cev in
        let (Dom_comp (fp_inner, dom_ev_inner)) = dom_comp param fn fm_inner cev_inner in
        Dom_comp
          (Suc (fp_inner, Inject fg, Suc (Zero, F.cod param fg)), Suc (dom_ev_inner, F.dom fg))

  type (_, _, _, _, _, _, _, _, _) dom_uncomp =
    | Dom_uncomp :
        ('param, 'b, 'n, 'c, 'y, 'r, 'z) t
        * ('param, 'a, 'm, 'b, 'x, 'q, 'y) t
        * ('a, 'm, 'b, 'n, 'c, 'mn) Dom.comp
        -> ('param, 'a, 'mn, 'c, 'x, 'q, 'y, 'r, 'z) dom_uncomp

  let rec dom_uncomp : type param a mn c x q y r z rq.
      param Param.t ->
      (x, q, y, r, z, rq) Cod.comp ->
      (param, a, mn, c, x, rq, z) t ->
      (param, a, mn, c, x, q, y, r, z) dom_uncomp =
   fun param cev fmn ->
    match cev with
    | Zero -> Dom_uncomp (fmn, Zero (src fmn), Zero)
    | Suc (cev_inner, edge_cev) ->
        let (Suc (fmn_rest, Inject fg, Suc (Zero, edge_fg))) = fmn in
        let Eq = C.tgt_uniq edge_fg edge_cev in
        let (Dom_uncomp (fn, fm_inner, dom_ev_rec)) = dom_uncomp param cev_inner fmn_rest in
        Dom_uncomp
          (fn, Suc (fm_inner, Inject fg, Suc (Zero, F.cod param fg)), Suc (dom_ev_rec, F.dom fg))

  (* Forwards version *)
  type (_, _, _, _, _, _, _) fwd_t =
    | Zero : ('param, 'a, 'x) F.Obj.t -> ('param, 'a, 'a Dom.id, 'a, 'x, 'x Cod.id, 'x) fwd_t
    | Suc :
        ('param, 'a, 'g, 'a1, 'x1, 'n1, 'x) F.t * ('param, 'a1, 'm, 'b, 'x, 'n2, 'x1) fwd_t
        -> ('param, 'a, ('g, 'm) cons, 'b, 'x, ('n1, 'n2) cons, 'y) fwd_t
end

(* Intrinsically well-typed maps whose domains are paths in a free category.  This is the analogue of Word.Map for free categories: a recursive trie keyed by paths, with values parametrized by the path's source, morphism shape, and target (plus one ambient parameter), so the value family is a Fam4 rather than a Fam2.

   Each internal map fixes its target object 'tgt; the keys are paths from any source to 'tgt.  The trie is walked target-side-first: the top-level edge-map (DM) is keyed by edges into 'tgt, and the accumulator path grows on the source side via snoc.  Concretely, converting an input path to a forward representation in target-first order via [to_fwd] then walking that with [Tbwd.append] evidence ties the recursion together. *)

module rec PathMapDef : functor (Q : Quiver) (QM : MAP3_MAKER with module Key = Q) (F : Fam4) -> sig
  module M : sig
    type ('outer_p, 'a, 'g, 'b) t =
      | Wrapmap :
          ('p, 'a, ('m, 'g) snoc, 'tgt) PathMapDef(Q)(QM)(F).map
          -> ('p * 'm * 'tgt * 'b, 'a, 'g, 'b) t
  end

  module DM : module type of QM.Make (M)

  type ('p, 'src, 'm, 'tgt) map =
    | Empty
    | Entry of ('p, 'src, 'm, 'tgt) F.t option * ('p * 'm * 'tgt * 'src) DM.t
end =
functor
  (Q : Quiver)
  (QM : MAP3_MAKER with module Key = Q)
  (F : Fam4)
  ->
  struct
    module M = struct
      type ('outer_p, 'a, 'g, 'b) t =
        | Wrapmap :
            ('p, 'a, ('m, 'g) snoc, 'tgt) PathMapDef(Q)(QM)(F).map
            -> ('p * 'm * 'tgt * 'b, 'a, 'g, 'b) t
    end

    module DM = QM.Make (M)

    type ('p, 'src, 'm, 'tgt) map =
      | Empty
      | Entry of ('p, 'src, 'm, 'tgt) F.t option * ('p * 'm * 'tgt * 'src) DM.t
  end

module PathMapInternal (Q : Quiver) (QM : MAP3_MAKER with module Key = Q) (F : Fam4) = struct
  module Cat = Make (Q)
  module Map = PathMapDef (Q) (QM) (F)

  let rec find_opt : type p src cur fwd_rest m_acc m_full tgt.
      (src, fwd_rest, cur, m_acc, tgt, m_full) Cat.bcomp ->
      (p, cur, m_acc, tgt) Map.map ->
      (p, src, m_full, tgt) F.t option =
   fun bcomp m ->
    let open Monad.Ops (Monad.Maybe) in
    match m with
    | Empty -> None
    | Entry (x, dm) -> (
        match bcomp with
        | Zero -> x
        | Suc (g, rest_bcomp) ->
            let* (Map.M.Wrapmap sub) = Map.DM.find_opt g dm in
            find_opt rest_bcomp sub)

  let rec add : type p src cur fwd_rest m_acc m_full tgt.
      (src, fwd_rest, cur, m_acc, tgt, m_full) Cat.bcomp ->
      (p, src, m_full, tgt) F.t ->
      (p, cur, m_acc, tgt) Map.map ->
      (p, cur, m_acc, tgt) Map.map =
   fun bcomp value m ->
    match (bcomp, m) with
    | Zero, Empty -> Entry (Some value, Map.DM.empty)
    | Zero, Entry (_, dm) -> Entry (Some value, dm)
    | Suc (g, rest_bcomp), Empty ->
        Entry (None, Map.DM.add g (Map.M.Wrapmap (add rest_bcomp value Empty)) Map.DM.empty)
    | Suc (g, rest_bcomp), Entry (e, dm) ->
        Entry
          ( e,
            Map.DM.update g
              (function
                | Some (Map.M.Wrapmap sub) -> Some (Map.M.Wrapmap (add rest_bcomp value sub))
                | None -> Some (Map.M.Wrapmap (add rest_bcomp value Empty)))
              dm )

  let rec update : type p src cur fwd_rest m_acc m_full tgt.
      (src, fwd_rest, cur, m_acc, tgt, m_full) Cat.bcomp ->
      ((p, src, m_full, tgt) F.t option -> (p, src, m_full, tgt) F.t option) ->
      (p, cur, m_acc, tgt) Map.map ->
      (p, cur, m_acc, tgt) Map.map =
   fun bcomp f m ->
    match (bcomp, m) with
    | Zero, Empty -> Entry (f None, Map.DM.empty)
    | Zero, Entry (x, dm) -> Entry (f x, dm)
    | Suc (g, rest_bcomp), Empty ->
        Entry (None, Map.DM.add g (Map.M.Wrapmap (update rest_bcomp f Empty)) Map.DM.empty)
    | Suc (g, rest_bcomp), Entry (e, dm) ->
        Entry
          ( e,
            Map.DM.update g
              (function
                | Some (Map.M.Wrapmap sub) -> Some (Map.M.Wrapmap (update rest_bcomp f sub))
                | None -> Some (Map.M.Wrapmap (update rest_bcomp f Empty)))
              dm )

  let rec remove : type p src cur fwd_rest m_acc tgt.
      (src, fwd_rest, cur) Cat.fwd -> (p, cur, m_acc, tgt) Map.map -> (p, cur, m_acc, tgt) Map.map =
   fun fwd m ->
    match (fwd, m) with
    | _, Empty -> Empty
    | Nil, Entry (_, dm) -> Entry (None, dm)
    | Cons (g_edge, rest_fwd), Entry (e, dm) ->
        Entry
          ( e,
            Map.DM.update g_edge
              (Option.map (fun (Map.M.Wrapmap sub) -> Map.M.Wrapmap (remove rest_fwd sub)))
              dm )

  type 'p mapper = {
    map :
      'src 'm 'tgt. ('src, 'm, 'tgt) Cat.t -> ('p, 'src, 'm, 'tgt) F.t -> ('p, 'src, 'm, 'tgt) F.t;
  }

  let rec map : type p src m tgt.
      p mapper -> (src, m, tgt) Cat.t -> (p, src, m, tgt) Map.map -> (p, src, m, tgt) Map.map =
   fun f accum_path m ->
    match m with
    | Empty -> Empty
    | Entry (x, dm) ->
        let map : type a b c.
            (a, b, c) Q.t ->
            (p * m * tgt * src, a, b, c) Map.M.t ->
            (p * m * tgt * src, a, b, c) Map.M.t =
         fun edge (Map.M.Wrapmap sub) -> Map.M.Wrapmap (map f (Cat.suc accum_path edge) sub) in
        Entry (Option.map (f.map accum_path) x, Map.DM.map { map } dm)

  type 'p iterator = {
    it : 'src 'm 'tgt. ('src, 'm, 'tgt) Cat.t -> ('p, 'src, 'm, 'tgt) F.t -> unit;
  }

  let rec iter : type p src m tgt.
      p iterator -> (src, m, tgt) Cat.t -> (p, src, m, tgt) Map.map -> unit =
   fun f accum_path m ->
    match m with
    | Empty -> ()
    | Entry (x, dm) ->
        let it : type a b c. (a, b, c) Q.t -> (p * m * tgt * src, a, b, c) Map.M.t -> unit =
         fun edge (Map.M.Wrapmap sub) -> iter f (Cat.suc accum_path edge) sub in
        Option.iter (f.it accum_path) x;
        Map.DM.iter { it } dm
end

(* The user-facing functor.  Takes a quiver Q, an object-map maker QObjMap, and an edge-map maker QM, and produces a MAP3_MAKER keyed by paths in the free category Make(Q).  Internally each entry of the top-level object-map QObjMap holds a fixed-target trie of paths; dispatching on the target object recovers a MAP3_MAKER interface (single-parameter ['p t]) from the underlying per-target structure. *)

module Map
    (Q : Quiver)
    (QObjMap : MAP_MAKER with module Key := Q.Obj)
    (QM : MAP3_MAKER with module Key := Q) : MAP3_MAKER with module Key := Make(Q) = struct
  module Cat = Make (Q)

  module Make (F : Fam4) = struct
    module QM2 = struct
      module Key = Q
      include QM
    end

    module I = PathMapInternal (Q) (QM2) (F)

    (* The Fam2 fed to the object-map: at each target object 'tgt, store the fixed-target trie. *)
    module ObjF = struct
      type ('p, 'tgt) t = ('p, 'tgt, 'tgt id, 'tgt) I.Map.map
    end

    module ObjMap = QObjMap.Make (ObjF)

    type 'p t = 'p ObjMap.t

    let empty : type p. p t = ObjMap.empty

    let find_opt : type p src m tgt. (src, m, tgt) Cat.t -> p t -> (p, src, m, tgt) F.t option =
     fun path t ->
      let open Monad.Ops (Monad.Maybe) in
      let* path_map = ObjMap.find_opt (Cat.tgt path) t in
      let (To_fwd (_, bcomp)) = Cat.to_fwd path in
      I.find_opt bcomp path_map

    let add : type p src m tgt. (src, m, tgt) Cat.t -> (p, src, m, tgt) F.t -> p t -> p t =
     fun path value t ->
      let (To_fwd (_, bcomp)) = Cat.to_fwd path in
      ObjMap.update (Cat.tgt path)
        (function
          | None -> Some (I.add bcomp value I.Map.Empty)
          | Some path_map -> Some (I.add bcomp value path_map))
        t

    let update : type p src m tgt.
        (src, m, tgt) Cat.t ->
        ((p, src, m, tgt) F.t option -> (p, src, m, tgt) F.t option) ->
        p t ->
        p t =
     fun path f t ->
      let (To_fwd (_, bcomp)) = Cat.to_fwd path in
      ObjMap.update (Cat.tgt path)
        (function
          | None -> Some (I.update bcomp f I.Map.Empty)
          | Some path_map -> Some (I.update bcomp f path_map))
        t

    let remove : type p src m tgt. (src, m, tgt) Cat.t -> p t -> p t =
     fun path t ->
      let (To_fwd (fwd, _)) = Cat.to_fwd path in
      ObjMap.update (Cat.tgt path) (Option.map (fun path_map -> I.remove fwd path_map)) t

    type 'p mapper = 'p I.mapper = {
      map :
        'src 'm 'tgt. ('src, 'm, 'tgt) Cat.t -> ('p, 'src, 'm, 'tgt) F.t -> ('p, 'src, 'm, 'tgt) F.t;
    }

    let map : type p. p mapper -> p t -> p t =
     fun f t -> ObjMap.map { map = (fun tgt_obj path_map -> I.map f (Cat.id tgt_obj) path_map) } t

    type 'p iterator = 'p I.iterator = {
      it : 'src 'm 'tgt. ('src, 'm, 'tgt) Cat.t -> ('p, 'src, 'm, 'tgt) F.t -> unit;
    }

    let iter : type p. p iterator -> p t -> unit =
     fun f t -> ObjMap.iter { it = (fun tgt_obj path_map -> I.iter f (Cat.id tgt_obj) path_map) } t
  end
end
