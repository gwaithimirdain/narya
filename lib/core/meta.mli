open Util
open Signatures
open Dimbwd
open Energy
open Origin

type ('a, 'b, 's) t

val make_def : string -> string option -> 'a N.t -> 'b Dbwd.t -> 's energy -> ('a, 'b, 's) t
val make_hole : 'a N.t -> 'b Dbwd.t -> 's energy -> ('a, 'b, 's) t
val remake : (File.t -> File.t) -> ('a, 'b, 's) t -> ('a, 'b, 's) t
val name : ('a, 'b, 's) t -> string
val origin : ('a, 'b, 's) t -> Origin.t

val compare :
  ('a1, 'b1, 's1) t -> ('a2, 'b2, 's2) t -> ('a1 * 'b1 * 's1, 'a2 * 'b2 * 's2) Eq.compare

type wrapped = Wrap : ('a, 'b, 's) t -> wrapped

module Wrapped : sig
  type t = wrapped

  val compare : t -> t -> int
end

module WrapSet : module type of Set.Make (Wrapped)

val hole_number : ('a, 'b, 's) t -> int

module Table : sig
  type ('a, 'b, 's) key = ('a, 'b, 's) t

  module Make (F : Fam4) : sig
    type _ entry = Entry : ('a, 'b, 's) t * ('x, 'a, 'b, 's) F.t -> 'x entry
    type 'x t

    val make : unit -> 'x t
    val find_opt : ('a, 'b, 's) key -> 'x t -> ('x, 'a, 'b, 's) F.t option
    val find_hole_opt : int -> 'x t -> 'x entry option

    val update :
      ('a, 'b, 's) key ->
      (('x, 'a, 'b, 's) F.t option -> ('x, 'a, 'b, 's) F.t option) ->
      'x t ->
      unit

    val add : ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> 'x t -> unit

    type ('x, 'acc) folder = {
      fold : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> 'acc -> 'acc;
    }

    val fold : ('x, 'acc) folder -> 'x t -> 'acc -> 'acc
    val fold_current : ('x, 'acc) folder -> 'x t -> 'acc -> 'acc

    type 'x file_entry

    val find_file : File.t -> 'x t -> 'x file_entry
    val add_file : File.t -> 'a file_entry -> 'a t -> unit
    val to_channel_file : Out_channel.t -> File.t -> 'x t -> Marshal.extern_flags list -> unit

    type 'x mapper = {
      map : 'a 'b 's. ('a, 'b, 's) key -> ('x, 'a, 'b, 's) F.t -> ('x, 'a, 'b, 's) F.t;
    }

    val from_channel_file : In_channel.t -> 'x mapper -> File.t -> 'x t -> 'x file_entry
  end
end
