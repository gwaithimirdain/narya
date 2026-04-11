open Util
open Signatures

module Mode : sig
  type _ t

  module Mode : sig
    type nonrec 'a t = 'a t
  end

  val compare : 'm t -> 'n t -> ('m, 'n) Eq.compare

  type wrapped = Wrap : 'mode t -> wrapped

  val to_string : 'a t -> string
  val all : (string * wrapped) list
  val unique : unit -> wrapped option

  module Map : MAP_MAKER with module Key := Mode
end

type 'mode id_modality

module Modality : sig
  type (_, _, _) t

  val cod : ('a, 'm, 'b) t -> 'b Mode.t
  val dom : ('a, 'm, 'b) t -> 'a Mode.t

  type (_, _) wrapped = Wrap : ('a, 'm, 'b) t -> ('a, 'b) wrapped
  type _ cod_wrapped = Wrap : ('a, 'm, 'b) t -> 'a cod_wrapped
  type _ dom_wrapped = Wrap : ('a, 'm, 'b) t -> 'b dom_wrapped

  val id : 'm Mode.t -> ('m, 'm id_modality, 'm) t

  type (_, _, _) comp

  type (_, _, _, _) composed =
    | Composed : ('a, 'nm, 'b) t * ('n, 'm, 'nm) comp -> ('a, 'n, 'm, 'b) composed

  val comp : ('b, 'n, 'c) t -> ('a, 'm, 'b) t -> ('a, 'n, 'm, 'c) composed
  val eq_of_comp_id_right : ('m, 'a id_modality, 'n) comp -> ('m, 'n) Util.Eq.t
  val eq_of_comp_id_left : ('a id_modality, 'm, 'n) comp -> ('m, 'n) Util.Eq.t
  val comp_id_right : ('a, 'm, 'b) t -> ('m, 'a id_modality, 'm) comp
  val comp_id_left : ('a, 'm, 'b) t -> ('b id_modality, 'm, 'm) comp

  val comp_assocl :
    ('m, 'n, 'mn) comp -> ('n, 'p, 'np) comp -> ('m, 'np, 'mnp) comp -> ('mn, 'p, 'mnp) comp

  val comp_assocr :
    ('m, 'n, 'mn) comp -> ('n, 'p, 'np) comp -> ('mn, 'p, 'mnp) comp -> ('m, 'np, 'mnp) comp

  val compare : ('a, 'm, 'b) t -> ('c, 'n, 'd) t -> ('a * 'm * 'b, 'c * 'n * 'd) Util.Eq.compare
  val compare_id : ('a, 'm, 'b) t -> ('a * 'm, 'b * 'a id_modality) Util.Eq.compare
  val to_colon : ('a, 'm, 'b) t -> [ `Single of string | `Double of string ]
  val to_string : ('a, 'm, 'b) t -> string
  val locker : 'a Mode.t -> ('a, 'a) wrapped

  type (_, _, _, _) factored =
    | Factored : ('b, 'r, 'c) t * ('r, 'n, 'rn) comp -> ('b, 'c, 'n, 'rn) factored

  val factor : ('a, 'rn, 'c) t -> ('a, 'n, 'b) t -> ('b, 'c, 'n, 'rn) factored option

  type (_, _, _, _) pushout =
    | Pushout :
        ('b, 'p, 'd) t * ('c, 'q, 'd) t * ('p, 'm, 'r) comp * ('q, 'n, 'r) comp
        -> ('m, 'n, 'b, 'c) pushout
    | No_pushout

  val pushout : ('a, 'm, 'b) t -> ('a, 'n, 'c) t -> ('m, 'n, 'b, 'c) pushout

  module Cube : (F : Fam3) -> sig
    module Parent : sig
      type ('a, 'm, 'b) modality_t = ('a, 'm, 'b) t
    end

    open Parent

    type (_, _, _, _) t =
      | Modal :
          ('dom, 'modality, 'mode) modality_t * ('n, ('dom, 'a, 'b) F.t) Dim.CubeOf.t
          -> ('n, 'mode, 'a, 'b) t
  end

  type pre

  val pre_id : pre
  val of_pre_dom : pre -> 'a Mode.t -> 'a cod_wrapped option
  val of_pre_cod : pre -> 'b Mode.t -> 'b dom_wrapped option
  val pre_to_colon : pre -> [ `Single of string | `Double of string ]
  val pre_to_string : pre -> string
  val compare_pre : pre -> ('dom, 'modality, 'cod) t -> bool
  val compare_pre_id : pre -> bool
  val pre_of_colon : [ `Single of string | `Double of string ] -> pre option
end

module Modalcell : sig
  type (_, _, _, _) t

  type (_, _, _, _, _, _) find_unique =
    | Unique : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b, 'a, 'n, 'b) find_unique
    | Nonunique : ('a, 'm, 'b, 'c, 'n, 'd) find_unique

  val find_unique :
    ('a, 'm, 'b) Modality.t -> ('c, 'n, 'd) Modality.t -> ('a, 'm, 'b, 'c, 'n, 'd) find_unique

  val id : ('dom, 'modality, 'cod) Modality.t -> ('dom, 'modality, 'modality, 'cod) t
  val id2 : 'mode Mode.t -> ('mode, 'mode id_modality, 'mode id_modality, 'mode) t

  val compare :
    ('dom1, 'mu1, 'nu1, 'cod1) t ->
    ('dom2, 'mu2, 'nu2, 'cod2) t ->
    ('dom1 * 'mu1 * 'nu1 * 'cod1, 'dom2 * 'mu2 * 'nu2 * 'cod2) Util.Eq.compare

  val compare_id :
    ('dom, 'mu, 'nu, 'cod) t ->
    ('dom * 'mu * 'nu, 'cod * 'dom id_modality * 'dom id_modality) Util.Eq.compare

  type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped
  type (_, _, _) cod_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) cod_wrapped
  type (_, _, _) dom_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) dom_wrapped
  type _ cod2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'a cod2_wrapped
  type _ dom2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'b dom2_wrapped

  val hdom : ('a, 'm, 'n, 'b) t -> 'a Mode.t
  val hcod : ('a, 'm, 'n, 'b) t -> 'b Mode.t
  val vdom : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) Modality.t
  val vcod : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) Modality.t

  val hcomp :
    ('m, 'r, 'mr) Modality.comp ->
    ('n, 's, 'ns) Modality.comp ->
    ('b, 'm, 'n, 'c) t ->
    ('a, 'r, 's, 'b) t ->
    ('a, 'mr, 'ns, 'c) t

  val hcomp_wrapped : ('b, 'm, 'n, 'c) t -> ('a, 'r, 's, 'b) t -> ('a, 'c) wrapped

  val postwhisker :
    ('m, 'r, 'mr) Modality.comp ->
    ('m, 's, 'ms) Modality.comp ->
    ('b, 'm, 'c) Modality.t ->
    ('a, 'r, 's, 'b) t ->
    ('a, 'mr, 'ms, 'c) t

  val postwhisker_wrapped : ('b, 'm, 'c) Modality.t -> ('a, 'r, 's, 'b) t -> ('a, 'c) wrapped

  val prewhisker :
    ('m, 'r, 'mr) Modality.comp ->
    ('n, 'r, 'nr) Modality.comp ->
    ('b, 'm, 'n, 'c) t ->
    ('a, 'r, 'b) Modality.t ->
    ('a, 'mr, 'nr, 'c) t

  val prewhisker_wrapped : ('b, 'm, 'n, 'c) t -> ('a, 'r, 'b) Modality.t -> ('a, 'c) wrapped
  val vcomp : ('a, 'n, 'r, 'b) t -> ('a, 'm, 'n, 'b) t -> ('a, 'm, 'r, 'b) t

  val vcomp_extending :
    ('k, 'n, 'kn) Modality.comp ->
    ('a, 'n, 's, 'c) t ->
    ('a, 'm, 'kn, 'b) t ->
    ('a, 'm, 'c) cod_wrapped

  val to_string : ('a, 'm, 'n, 'b) t -> string
end

(* MODALTODO: Get rid of these once the whitebox tests can choose their own theories. *)

type test_mode

val test_mode : test_mode Mode.t
val id_modality : (test_mode, test_mode id_modality, test_mode) Modality.t
