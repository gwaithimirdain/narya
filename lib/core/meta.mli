open Util
open Signatures
open Modal
open Dimbwd
open Energy
open Origin

type ('mode, 'a, 'b, 's) t

val make_def :
  string ->
  string option ->
  'mode Mode.t ->
  'a N.t ->
  'b Dbwd.t ->
  's energy ->
  ('mode, 'a, 'b, 's) t

val make_hole : 'mode Mode.t -> 'a N.t -> 'b Dbwd.t -> 's energy -> ('mode, 'a, 'b, 's) t
val remake : (File.t -> File.t) -> ('mode, 'a, 'b, 's) t -> ('mode, 'a, 'b, 's) t
val name : ('mode, 'a, 'b, 's) t -> string
val origin : ('mode, 'a, 'b, 's) t -> Origin.t

val compare :
  ('m1, 'a1, 'b1, 's1) t ->
  ('m2, 'a2, 'b2, 's2) t ->
  ('m1 * 'a1 * 'b1 * 's1, 'm2 * 'a2 * 'b2 * 's2) Eq.compare

type wrapped = Wrap : ('mode, 'a, 'b, 's) t -> wrapped

module Wrapped : sig
  type t = wrapped

  val compare : t -> t -> int
end

module WrapSet : module type of Set.Make (Wrapped)

val hole_number : ('mode, 'a, 'b, 's) t -> int

module Table : sig
  type ('mode, 'a, 'b, 's) key = ('mode, 'a, 'b, 's) t

  module Make (F : Fam5) : sig
    type _ entry = Entry : ('mode, 'a, 'b, 's) t * ('x, 'mode, 'a, 'b, 's) F.t -> 'x entry
    type 'x t

    val make : unit -> 'x t
    val find_opt : ('mode, 'a, 'b, 's) key -> 'x t -> ('x, 'mode, 'a, 'b, 's) F.t option
    val find_hole_opt : int -> 'x t -> 'x entry option
    val add : ('mode, 'a, 'b, 's) key -> ('x, 'mode, 'a, 'b, 's) F.t -> 'x t -> unit

    type ('x, 'acc) folder = {
      fold : 'mode 'a 'b 's. ('mode, 'a, 'b, 's) key -> ('x, 'mode, 'a, 'b, 's) F.t -> 'acc -> 'acc;
    }

    val fold : ('x, 'acc) folder -> 'x t -> 'acc -> 'acc
    val fold_current : ('x, 'acc) folder -> 'x t -> 'acc -> 'acc

    type 'x origin_entry

    val find_file : File.t -> 'x t -> 'x origin_entry
    val add_file : File.t -> 'a origin_entry -> 'a t -> unit
    val to_channel_origin : Out_channel.t -> Origin.t -> 'x t -> Marshal.extern_flags list -> unit

    type 'x mapper = {
      map :
        'mode 'a 'b 's.
        ('mode, 'a, 'b, 's) key -> ('x, 'mode, 'a, 'b, 's) F.t -> ('x, 'mode, 'a, 'b, 's) F.t;
    }

    val from_istream_origin : Istream.t -> 'x mapper -> Origin.t -> 'x t -> 'x origin_entry
  end
end
