open Util
open Signatures
open Dimbwd
open Energy

type sort = [ `Hole | `Def of string * string option ]
type ('b, 's) t

val make : Compunit.t -> sort -> 'b Dbwd.t -> 's energy -> ('b, 's) t
val remake : (Compunit.t -> Compunit.t) -> ('b, 's) t -> ('b, 's) t
val name : ('b, 's) t -> string
val compare : ('b1, 's1) t -> ('b2, 's2) t -> ('b1 * 's1, 'b2 * 's2) Eq.compare

type _ key = MetaKey : ('b, 's) t -> ('b * 's) key

module Key : sig
  type 'b t = 'b key
end

module Map : sig
  module Key = Key

  module Make : functor (F : Fam2) -> sig
    include MAP with module Key := Key and module F := F

    val to_channel_unit : Out_channel.t -> Compunit.t -> 'b t -> Marshal.extern_flags list -> unit
    val from_channel_unit : In_channel.t -> 'b mapper -> Compunit.t -> 'b t -> 'b t
  end
end
