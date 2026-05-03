open Signatures

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
