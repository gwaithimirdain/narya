module File : sig
  type t

  val make : [ `File of string | `Other of string ] -> t
  val get : string -> t
  val to_string : t -> [ `File of string | `Other of string ]
end

module Instant : sig
  type t

  val of_int : int -> t
  val ( <= ) : t -> t -> bool
end

module Origin : sig
  type t = Top | File of File.t | Instant of Instant.t

  val to_string : t -> string
  val current : unit -> t
  val holes_allowed : unit -> (unit, [ `File of string | `Other of string ]) Result.t
  val run : (unit -> 'a) -> 'a
  val with_file : holes_allowed:bool -> File.t -> (unit -> 'a) -> 'a
  val set_interactive : unit -> unit
  val undo : unit -> [ `Ok | `No_past | `Not_interactive ]
  val do_command : (unit -> 'a) -> 'a
  val do_command_then_undo : (unit -> 'a) -> 'a
  val rewind_command : Instant.t -> (unit -> 'a) -> 'a
  val rewind_command_then_undo : Instant.t -> (unit -> 'a) -> 'a
end

module Versioned : sig
  type 'a t

  val make : default:(unit -> 'a) -> inherit_values:bool -> 'a t
  val get_at : 'a t -> Origin.t -> 'a option
  val get : 'a t -> 'a
  val set : 'a t -> 'a -> unit
  val modify : 'a t -> ('a -> 'a) -> unit
  val set_file : 'a t -> File.t -> 'a -> unit
  val fold : 'a t -> ('acc -> 'a -> 'acc) -> 'acc -> 'acc
end
