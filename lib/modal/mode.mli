open Util
open Signatures
open Dim

type _ t

val not_unit : 'a t -> ('a, unit) Eq.t -> 'b
val compare : 'm t -> 'n t -> ('m, 'n) Eq.compare

type wrapped = Wrap : 'mode t -> wrapped

val name : 'a t -> string
val all : unit -> (string * wrapped) list
val unique : unit -> wrapped option

(* Which directions a mode forbids parametricity (degeneracies) in.  Analogous to a modality generator's nonparametricity (Modality.Generator.nonparametric), but attached to the mode itself: it is checked whenever a degeneracy is typechecked, independently of any locking behavior induced by modalities. *)
val nonparametric : 'a t -> D.wrapped

(* Whether a degeneracy is allowed to act at a given mode: none of the directions it degenerates may lie in the mode's nonparametric directions. *)
val allows_deg : 'a t -> ('m, 'n) deg -> bool

module Mode : sig
  type nonrec 'a t = 'a t
end

module Map : MAP_MAKER with module Key := Mode

module type Generator = sig
  val name : string ref

  (* Which directions this mode forbids parametricity in *)
  type nonparametric

  val nonparametric : nonparametric D.t
end

module type Generated = sig
  module G : Generator

  type t

  val mode : t Mode.t
end

module Generate : functor (G : Generator) -> Generated with module G := G
