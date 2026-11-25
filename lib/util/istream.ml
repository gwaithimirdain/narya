(* Input streams: an abstraction of channels and strings, things that can be marshaled from. *)

type t = Channel of In_channel.t | Bytes of { data : bytes; mutable pos : int }

let string str = Bytes { data = Bytes.of_string str; pos = 0 }

(* Make an input stream from a string that should consist of a sequence of complete marshaled values followed by the given trailer, returning None if it doesn't.  Since this checks only the framing and not the contents, it doesn't catch corruption, but it does catch truncation, so that a stream read up to its trailer never runs out partway through. *)
let framed_string str ~trailer =
  let data = Bytes.of_string str in
  let body = Bytes.length data - String.length trailer in
  let rec complete pos =
    if pos = body then true
    else if body - pos < Marshal.header_size then false
    else
      (* Marshal.total_size raises Failure on a bad header, but we've checked there are enough bytes to read the header. *)
      match Marshal.total_size data pos with
      | size -> size <= body - pos && complete (pos + size)
      | exception Failure _ -> false in
  if body >= 0 && Bytes.sub_string data body (String.length trailer) = trailer && complete 0 then
    Some (Bytes { data; pos = 0 })
  else None

let unmarshal = function
  | Channel chan -> Marshal.from_channel chan
  | Bytes s ->
      let x = Marshal.from_bytes s.data s.pos in
      s.pos <- s.pos + Marshal.total_size s.data s.pos;
      x
