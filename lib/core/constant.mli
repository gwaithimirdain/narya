open Origin

module Constant : sig
  type t

  val compare : t -> t -> int
end

type t = Constant.t

val make : unit -> t
val remake : (File.t -> File.t) -> Constant.t -> Constant.t

module Table : sig
  type 'a t

  val make : unit -> 'a t
  val find_opt : Constant.t -> 'a t -> 'a option
  val add : Constant.t -> 'a -> 'a t -> unit

  type 'a file_entry

  val find_file : File.t -> 'a t -> 'a file_entry
  val add_file : File.t -> 'a file_entry -> 'a t -> unit
  val to_channel_file : out_channel -> File.t -> 'a t -> Marshal.extern_flags list -> unit
  val from_channel_file : in_channel -> ('a -> 'b) -> File.t -> 'b t -> 'b file_entry
end

module Map : module type of Map.Make (Constant)
