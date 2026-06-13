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

type ('x, 'm, 'y, 'a, 'b) filter_dim

type (_, _, _, _) has_filter =
  | Has_filter : ('x, 'm, 'y, 'a, 'b) filter_dim -> ('x, 'm, 'y, 'b) has_filter

val filter : ('x, 'm, 'y) t -> 'b D.t -> ('x, 'm, 'y, 'b) has_filter

val filter_uniq :
  ('x, 'm, 'y, 'a1, 'b) filter_dim -> ('x, 'm, 'y, 'a2, 'b) filter_dim -> ('a1, 'a2) Eq.t

(* A filter_dim by a modality 'm has the same source and target as 'm; this recovers modes that have been bound existentially elsewhere. *)
val filter_dim_modes :
  ('x, 'm, 'y, 'a, 'b) filter_dim -> ('x2, 'm, 'y2) t -> ('x, 'x2) Eq.t * ('y, 'y2) Eq.t

val filtered : 'b D.t -> ('x, 'm, 'y, 'a, 'b) filter_dim -> 'a D.t
val filter_id : 'mode Mode.t -> 'a D.t -> ('mode, 'mode id, 'mode, 'a, 'a) filter_dim
val eq_of_filter_id : ('mode, 'mode id, 'mode, 'a, 'b) filter_dim -> ('a, 'b) Eq.t
val filter_zero : ('x, 'm, 'y) t -> ('x, 'm, 'y, D.zero, D.zero) filter_dim
val filter_idempotent : ('x, 'm, 'y, 'a, 'b) filter_dim -> ('x, 'm, 'y, 'a, 'a) filter_dim

val filter_plus :
  ('a, 'c, 'ac) D.plus ->
  ('b, 'd, 'bd) D.plus ->
  ('x, 'm, 'y, 'a, 'b) filter_dim ->
  ('x, 'm, 'y, 'c, 'd) filter_dim ->
  ('x, 'm, 'y, 'ac, 'bd) filter_dim

type (_, _, _, _, _, _) filter_of_plus =
  | Filter_of_plus :
      ('a, 'c, 'ac) D.plus * ('x, 'm, 'y, 'a, 'b) filter_dim * ('x, 'm, 'y, 'c, 'd) filter_dim
      -> ('x, 'm, 'y, 'b, 'd, 'ac) filter_of_plus

val filter_of_plus :
  ('b, 'd, 'bd) D.plus ->
  ('x, 'm, 'y, 'ac, 'bd) filter_dim ->
  ('x, 'm, 'y, 'b, 'd, 'ac) filter_of_plus

type (_, _, _, _, _, _) filter_of_plus' =
  | Filter_of_plus' :
      ('b, 'c, 'bc) D.plus * ('bc, 'd) perm * ('x, 'm, 'y, 'a, 'b) filter_dim
      -> ('x, 'm, 'y, 'a, 'c, 'd) filter_of_plus'

val filter_of_plus' :
  'd D.t ->
  ('a, 'c, 'ac) D.plus ->
  ('x, 'm, 'y, 'ac, 'd) filter_dim ->
  ('x, 'm, 'y, 'a, 'c, 'd) filter_of_plus'

type (_, _, _, _, _) filter_sface =
  | Filter_sface :
      ('d, 'a) sface * ('x, 'm, 'y, 'd, 'c) filter_dim
      -> ('x, 'm, 'y, 'a, 'c) filter_sface

val filter_sface :
  ('x, 'm, 'y, 'a, 'b) filter_dim -> ('c, 'b) sface -> ('x, 'm, 'y, 'a, 'c) filter_sface

type (_, _, _, _, _) filter_deg =
  | Filter_deg : ('d, 'a) deg * ('x, 'm, 'y, 'd, 'c) filter_dim -> ('x, 'm, 'y, 'a, 'c) filter_deg

val filter_deg : ('x, 'm, 'y, 'a, 'b) filter_dim -> ('c, 'b) deg -> ('x, 'm, 'y, 'a, 'c) filter_deg

type (_, _, _, _, _) filter_op =
  | Filter_op : ('d, 'a) op * ('x, 'm, 'y, 'd, 'c) filter_dim -> ('x, 'm, 'y, 'a, 'c) filter_op

val filter_op : ('x, 'm, 'y, 'a, 'b) filter_dim -> ('c, 'b) op -> ('x, 'm, 'y, 'a, 'c) filter_op

type (_, _, _, _, _) filter_perm =
  | Filter_perm :
      ('d, 'a) perm * ('x, 'm, 'y, 'd, 'c) filter_dim
      -> ('x, 'm, 'y, 'a, 'c) filter_perm

val filter_perm :
  ('x, 'm, 'y, 'a, 'b) filter_dim -> ('c, 'b) perm -> ('x, 'm, 'y, 'a, 'c) filter_perm

val deg_of_filter : 'b D.t -> ('x, 'm, 'y, 'a, 'b) filter_dim -> ('b, 'a) deg
val sface_of_filter : 'b D.t -> ('x, 'm, 'y, 'a, 'b) filter_dim -> ('a, 'b) sface

val filter_comp :
  ('x, 'm, 'y, 'n, 'z, 'nm) comp ->
  ('y, 'n, 'z, 'b, 'c) filter_dim ->
  ('x, 'm, 'y, 'a, 'b) filter_dim ->
  ('x, 'nm, 'z, 'a, 'c) filter_dim
