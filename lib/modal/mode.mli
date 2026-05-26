open Util
open Signatures

type _ t

val compare : 'm t -> 'n t -> ('m, 'n) Eq.compare

type wrapped = Wrap : 'mode t -> wrapped

val name : 'a t -> string
val all : unit -> (string * wrapped) list
val unique : unit -> wrapped option

module Mode : sig
  type nonrec 'a t = 'a t
end

module Map : MAP_MAKER with module Key := Mode

module type Generator = sig
  val name : string
end

module type Generated = sig
  module G : Generator

  type t

  val mode : t Mode.t
end

module Generate : functor (G : Generator) -> Generated with module G := G

val generate : string -> wrapped
