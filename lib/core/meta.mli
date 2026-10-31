open Util
open Signatures
open Modal
open Energy
open Origin
open Tctx

type ('mode, 'a, 'b, 's) t

(* A defined metavariable is either bound by a let or let rec, or else inserted automatically to hold the value of a case tree construct appearing bare in a kinetic position, in which case we record what sort of construct it was. *)
type sort = [ `Let | `Letrec of letrec_block | `Bare of string ]

(* The metavariables bound by the same "let rec … and …" block share a block identifier. *)
and letrec_block

val new_letrec_block : unit -> letrec_block
val run_owner : (unit -> 'x) -> 'x
val with_owner : Constant.t -> (unit -> 'x) -> 'x
val with_owner_of : ('mode, 'a, 'b, 's) t -> (unit -> 'x) -> 'x

val make_def :
  ?loc:Asai.Range.t ->
  sort ->
  string option ->
  'mode Mode.t ->
  'a N.t ->
  ('mode, 'b) Tctx.t ->
  's energy ->
  ('mode, 'a, 'b, 's) t

val make_hole : 'mode Mode.t -> 'a N.t -> ('mode, 'b) Tctx.t -> 's energy -> ('mode, 'a, 'b, 's) t
val remake : (File.t -> File.t) -> ('mode, 'a, 'b, 's) t -> ('mode, 'a, 'b, 's) t
val mode : ('mode, 'a, 'b, 's) t -> 'mode Mode.t
val name : ?owner_name:(Constant.t -> string) -> ('mode, 'a, 'b, 's) t -> string
val sort_of : ('mode, 'a, 'b, 's) t -> sort option
val is_bare : ('mode, 'a, 'b, 's) t -> bool
val letrec_siblings : ('m1, 'a1, 'b1, 's1) t -> ('m2, 'a2, 'b2, 's2) t -> bool
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
module WrapMap : module type of Map.Make (Wrapped)

val hole_number : ('mode, 'a, 'b, 's) t -> int

module Table : sig
  type ('mode, 'a, 'b, 's) key = ('mode, 'a, 'b, 's) t

  module Make (F : Fam5) : sig
    type 'x t

    val make : unit -> 'x t
    val find_opt : ('mode, 'a, 'b, 's) key -> 'x t -> ('x, 'mode, 'a, 'b, 's) F.t option

    type _ hole = Hole : ('mode, 'a, 'b, 's) key * ('x, 'mode, 'a, 'b, 's) F.t -> 'x hole

    val find_hole_opt : int -> 'x t -> 'x hole option
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
