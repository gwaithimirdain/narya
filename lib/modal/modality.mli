open Bwd
open Util
open Signatures
open Category

type ('a, 'm, 'b) gen

module Gen : Quiver with module Obj = Mode and type ('a, 'm, 'b) t = ('a, 'm, 'b) gen

module type Generator = sig
  type src
  type tgt

  val src : src Mode.t
  val tgt : tgt Mode.t
  val name : string
end

module type Generated = sig
  module G : Generator

  type t

  val modality : (G.src, t, G.tgt) gen
end

module Generate : functor (G : Generator) -> Generated with module G := G

type ('src, 'tgt) gen_wrapped = Wrap : ('src, 'morphism, 'tgt) Gen.t -> ('src, 'tgt) gen_wrapped

val generate : 'a Mode.t -> 'b Mode.t -> string -> ('a, 'b) gen_wrapped

include module type of Path.Make (Gen)
module Map : MAP3_MAKER with module Key := Path.Make(Gen)

module type Theory = sig
  val sharp : ('a, 'm, 'b) t -> bool
  val pellucid : ('a, 'm, 'b) t -> bool
  val transparent : ('a, 'm, 'b) t -> bool
  val translucent : ('a, 'm, 'b) t -> bool
end

val choose_theory : (module Theory) -> unit
val sharp : ('a, 'm, 'b) t -> bool
val pellucid : ('a, 'm, 'b) t -> bool
val transparent : ('a, 'm, 'b) t -> bool
val translucent : ('a, 'm, 'b) t -> bool

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
