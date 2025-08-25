(* Input streams: an abstraction of channels and strings, things that can be marshaled from. *)

type t = Channel of In_channel.t | Bytes of { data : bytes; mutable pos : int }

let string str = Bytes { data = Bytes.of_string str; pos = 0 }

let unmarshal = function
  | Channel chan -> Marshal.from_channel chan
  | Bytes s ->
      let x = Marshal.from_bytes s.data s.pos in
      s.pos <- s.pos + Marshal.total_size s.data s.pos;
      x
