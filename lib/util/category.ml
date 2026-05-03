(* Module signatures for type-level categories. *)

module type Category = sig
  (* The objects of the category are the types that satisfy this predicate. *)
  module Obj : Signatures.Comparable

  (* The morphisms are paths from one object to another with a "shape" recording the sequence of generators. *)
  type (_, _, _) t
  type wrapped = Wrap : ('src, 'shape, 'tgt) t -> wrapped

  val src : ('a, 'm, 'b) t -> 'a Obj.t
  val tgt : ('a, 'm, 'b) t -> 'b Obj.t

  val compare :
    ('a1, 'm1, 'b1) t -> ('a2, 'm2, 'b2) t -> ('a1 * 'm1 * 'b1, 'a2 * 'm2 * 'b2) Eq.compare

  (* Composition is defined as a relation: ('a, 'm, 'b, 'n, 'c, 'p) comp says that a morphism from 'a to 'b of shape 'm composed with one from 'b to 'c of shape 'n is a morphism from 'a to 'c of shape 'p. *)
  type (_, _, _, _, _, _) comp

  (* To compute a composite, we wrap up the output in a GADT. *)
  type (_, _, _, _, _) has_comp =
    | Comp : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b, 'n, 'c) has_comp

  (* As with Monoid, the choice of which arguments must be supplied and which can be deduced mirrors what happens for natural numbers/words. *)
  val comp : ('b, 'n, 'c) t -> ('a, 'm, 'b, 'n, 'c) has_comp
  val comp_right : 'b Obj.t -> ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('b, 'n, 'c) t
  val comp_left : ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'p, 'c) t -> ('a, 'm, 'b) t
  val comp_out : ('a, 'm, 'b) t -> ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'p, 'c) t

  (* Composites are unique *)
  val comp_uniq :
    ('a, 'm, 'b, 'n, 'c, 'p) comp -> ('a, 'm, 'b, 'n, 'c, 'q) comp -> ('p, 'q) Eq.t

  (* Identity morphisms *)
  type zero

  val id : 'a Obj.t -> ('a, zero, 'a) t
  val id_comp : ('b, 'n, 'c) t -> ('b, zero, 'b, 'n, 'c, 'n) comp
  val comp_id : ('a, 'm, 'b) t -> ('a, 'm, 'b, zero, 'b, 'm) comp

  (* Composition is associative *)
  val comp_assocl :
    ('a, 'm, 'b, 'n, 'c, 'mn) comp ->
    ('b, 'n, 'c, 'p, 'd, 'np) comp ->
    ('a, 'm, 'b, 'np, 'd, 'mnp) comp ->
    ('a, 'mn, 'c, 'p, 'd, 'mnp) comp

  val comp_assocr :
    ('a, 'm, 'b, 'n, 'c, 'mn) comp ->
    ('b, 'n, 'c, 'p, 'd, 'np) comp ->
    ('a, 'mn, 'c, 'p, 'd, 'mnp) comp ->
    ('a, 'm, 'b, 'np, 'd, 'mnp) comp
end
