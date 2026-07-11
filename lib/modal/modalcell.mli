open Util

type ('a, 'm, 'n, 'b) gen

module Gen : sig
  type ('a, 'm, 'n, 'b) t = ('a, 'm, 'n, 'b) gen

  val compare :
    ('dom1, 'mu1, 'nu1, 'cod1) t ->
    ('dom2, 'mu2, 'nu2, 'cod2) t ->
    ('dom1 * 'mu1 * 'nu1 * 'cod1, 'dom2 * 'mu2 * 'nu2 * 'cod2) Eq.compare
end

val generate : ('a, 'm, 'b) Modality.t -> ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) gen

type (_, _, _, _) t =
  | Gen : ('a, 'm, 'n, 'b) gen -> ('a, 'm, 'n, 'b) t
  | Id : ('a, 'm, 'b) Modality.t -> ('a, 'm, 'm, 'b) t
  | Hcomp :
      ('a, 'm, 'b, 'r, 'c, 'mr) Modality.comp
      * ('a, 'n, 'b, 's, 'c, 'ns) Modality.comp
      * ('b, 'r, 's, 'c) t
      * ('a, 'm, 'n, 'b) t
      -> ('a, 'mr, 'ns, 'c) t
  | Vcomp : ('a, 'n, 'r, 'b) t * ('a, 'm, 'n, 'b) t -> ('a, 'm, 'r, 'b) t

val of_gen : ('a, 'm, 'n, 'b) gen -> ('a, 'm, 'n, 'b) t

type (_, _, _, _) adjunction =
  | Adjunction : {
      left : ('a, 'f, 'b) Modality.t;
      right : ('b, 'g, 'a) Modality.t;
      right_left : ('a, 'f, 'b, 'g, 'a, 'gf) Modality.comp;
      unit : ('a, 'a Modality.id, 'gf, 'a) t;
      left_right : ('b, 'g, 'a, 'f, 'b, 'fg) Modality.comp;
      counit : ('b, 'fg, 'b Modality.id, 'b) t;
    }
      -> ('a, 'f, 'g, 'b) adjunction

type (_, _, _) sinister = Sinister : ('a, 'f, 'g, 'b) adjunction -> ('a, 'f, 'b) sinister
type _ any_adjunction = Any_adjunction : ('a, 'f, 'g, 'b) adjunction -> 'a any_adjunction

val id_adjunction : 'a Mode.t -> ('a, 'a Modality.id, 'a Modality.id, 'a) adjunction
val id_sinister : 'a Mode.t -> ('a, 'a Modality.id, 'a) sinister
val adj_left : ('a, 'f, 'g, 'b) adjunction -> ('a, 'f, 'b) Modality.t
val adj_right : ('a, 'f, 'g, 'b) adjunction -> ('b, 'g, 'a) Modality.t

val compare_adjunction_id :
  ('a, 'f, 'g, 'b) adjunction -> ('f * 'g * 'b, 'a Modality.id * 'a Modality.id * 'a) Eq.compare

type _ parametric_locker =
  | Locker : ('a, 'm, 'a) Modality.t * ('a, 'm, 'a Modality.id, 'a) t -> 'a parametric_locker

module type Theory = sig
  val sinister : ('a, 'm, 'b) Modality.t -> ('a, 'm, 'b) sinister option
  val compare : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'n, 'b) t -> bool
  val find_unique : ('a, 'm, 'b) Modality.t -> ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) t option
  val parametric_locker : 'a Mode.t -> ('a parametric_locker, string) Result.t
  val to_string : ('a, 'm, 'n, 'b) t -> string
end

val choose_theory : (module Theory) -> unit
val sinister : ('a, 'f, 'b) Modality.t -> ('a, 'f, 'b) sinister option

type (_, _, _, _, _, _) find_unique =
  | Unique : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b, 'a, 'n, 'b) find_unique

val find_unique :
  ('a, 'm, 'b) Modality.t -> ('c, 'n, 'd) Modality.t -> ('a, 'm, 'b, 'c, 'n, 'd) find_unique option

val id : ('dom, 'modality, 'cod) Modality.t -> ('dom, 'modality, 'modality, 'cod) t
val id2 : 'mode Mode.t -> ('mode, 'mode Modality.id, 'mode Modality.id, 'mode) t

val compare :
  ('dom1, 'mu1, 'nu1, 'cod1) t ->
  ('dom2, 'mu2, 'nu2, 'cod2) t ->
  ('dom1 * 'mu1 * 'nu1 * 'cod1, 'dom2 * 'mu2 * 'nu2 * 'cod2) Util.Eq.compare

val compare_id :
  ('dom, 'mu, 'nu, 'cod) t ->
  ('dom * 'mu * 'nu, 'cod * 'dom Modality.id * 'dom Modality.id) Util.Eq.compare

type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped
type (_, _, _) cod_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) cod_wrapped
type (_, _, _) dom_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) dom_wrapped
type _ cod2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'a cod2_wrapped
type _ dom2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'b dom2_wrapped

val hsrc : ('a, 'm, 'n, 'b) t -> 'a Mode.t
val htgt : ('a, 'm, 'n, 'b) t -> 'b Mode.t
val vsrc : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) Modality.t
val vtgt : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) Modality.t

val hcomp :
  ('a, 'm, 'b, 'r, 'c, 'mr) Modality.comp ->
  ('a, 'n, 'b, 's, 'c, 'ns) Modality.comp ->
  ('b, 'r, 's, 'c) t ->
  ('a, 'm, 'n, 'b) t ->
  ('a, 'mr, 'ns, 'c) t

val hcomp_wrapped : ('b, 'm, 'n, 'c) t -> ('a, 'r, 's, 'b) t -> ('a, 'c) wrapped

val postwhisker :
  ('a, 'r, 'b, 'm, 'c, 'mr) Modality.comp ->
  ('a, 's, 'b, 'm, 'c, 'ms) Modality.comp ->
  ('b, 'm, 'c) Modality.t ->
  ('a, 'r, 's, 'b) t ->
  ('a, 'mr, 'ms, 'c) t

val postwhisker_wrapped : ('b, 'm, 'c) Modality.t -> ('a, 'r, 's, 'b) t -> ('a, 'c) wrapped

val prewhisker :
  ('a, 'r, 'b, 'm, 'c, 'mr) Modality.comp ->
  ('a, 'r, 'b, 'n, 'c, 'nr) Modality.comp ->
  ('b, 'm, 'n, 'c) t ->
  ('a, 'r, 'b) Modality.t ->
  ('a, 'mr, 'nr, 'c) t

val prewhisker_wrapped : ('b, 'm, 'n, 'c) t -> ('a, 'r, 'b) Modality.t -> ('a, 'c) wrapped
val vcomp : ('a, 'n, 'r, 'b) t -> ('a, 'm, 'n, 'b) t -> ('a, 'm, 'r, 'b) t

val bprewhisker :
  ('a, 'r, 'b, 'm, 'c, 'mr) Modality.bcomp ->
  ('a, 'r, 'b, 'n, 'c, 'nr) Modality.bcomp ->
  ('b, 'm, 'n, 'c) t ->
  ('a, 'mr, 'nr, 'c) t

val vcomp_extending :
  ('c, 'k, 'b) Modality.t ->
  ('a, 'n, 'c, 'k, 'b, 'kn) Modality.comp ->
  ('a, 'n, 's, 'c) t ->
  ('a, 'm, 'kn, 'b) t ->
  ('a, 'm, 'b) cod_wrapped

val parametric_locker : 'a Mode.t -> 'a parametric_locker
val to_string : ('a, 'm, 'n, 'b) t -> string
