open Bwd
open Util
open Signatures
open Dim
open Category

type ('a, 'm, 'b) gen

module Gen : Quiver with module Obj = Mode and type ('a, 'm, 'b) t = ('a, 'm, 'b) gen

module type Generator = sig
  type src
  type tgt

  val src : src Mode.t
  val tgt : tgt Mode.t
  val name : string

  type nonparametric

  val nonparametric : nonparametric D.t
end

module type Generated = sig
  module G : Generator

  type t

  val modality : (G.src, t, G.tgt) gen
end

module Generate : functor (G : Generator) -> Generated with module G := G

type ('src, 'tgt) gen_wrapped = Wrap : ('src, 'morphism, 'tgt) Gen.t -> ('src, 'tgt) gen_wrapped

val generate : 'a Mode.t -> 'b Mode.t -> string -> 'e D.t -> ('a, 'b) gen_wrapped

include module type of Path.Make (Gen)
module Map : MAP3_MAKER with module Key := Path.Make(Gen)

val locker : 'a Mode.t -> ('a, 'a) wrapped

module Cube : (F : Signatures.Fam3) -> sig
  module Parent : sig
    type ('a, 'm, 'b) modality_t = ('a, 'm, 'b) t
  end

  type (_, _, _, _) t =
    | Modal :
        ('dom, 'modality, 'mode) Parent.modality_t * ('n, ('dom, 'a, 'b) F.t) Dim.CubeOf.t
        -> ('n, 'mode, 'a, 'b) t
end

val compare_id : ('x, 'm, 'y) t -> ('m * 'y, 'x id * 'x) Eq.compare

(* *)
val name_bwd : ('a, 'm, 'b) t -> string Bwd.t
val name : ('a, 'm, 'b) t -> string list

val of_name_tgt :
  ('s -> string) ->
  'a Mode.t ->
  's list ->
  ('a src_wrapped, [ `Not_found of 's | `Wrong_tgt of Mode.wrapped * 's * Mode.wrapped ]) result

val of_name_src_bwd :
  ('s -> string) ->
  's Bwd.t ->
  'a Mode.t ->
  ('a tgt_wrapped, [ `Not_found of 's | `Wrong_src of Mode.wrapped * 's * Mode.wrapped ]) result

val of_name_src :
  ('s -> string) ->
  's list ->
  'a Mode.t ->
  ('a tgt_wrapped, [ `Not_found of 's | `Wrong_src of Mode.wrapped * 's * Mode.wrapped ]) result

val to_string : ('a, 'm, 'b) t -> string

(* *)
val compare_name :
  ('s -> string) ->
  's list ->
  ('x, 'm, 'y) t ->
  ( unit,
    [ `Unequal of 'y src_wrapped
    | `Not_found of 's
    | `Wrong_tgt of Mode.wrapped * 's * Mode.wrapped ] )
  result

type ('m, 'e) nonparametric
type _ has_nonparametric = Nonparametric : ('m, 'e) nonparametric -> 'm has_nonparametric

val nonparametric : ('x, 'm, 'y) t -> 'm has_nonparametric

type ('m, 'a, 'b) filter_dim

val filter_zero : ('x, 'm, 'y) t -> ('m, D.zero, D.zero) filter_dim

type (_, _, _) filter_deg =
  | Filter_deg : ('d, 'a) deg * ('m, 'd, 'c) filter_dim -> ('m, 'a, 'c) filter_deg

val filter_deg : ('m, 'a, 'b) filter_dim -> ('c, 'b) deg -> ('m, 'a, 'c) filter_deg
