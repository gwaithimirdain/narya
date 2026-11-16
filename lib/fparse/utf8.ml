(* UTF-8 encoding. *)

module Encoder = struct
  type t = Uchar.t

  let to_string (u : Uchar.t) : string =
    let buf = Buffer.create 4 in
    Buffer.add_utf_8_uchar buf u;
    Buffer.contents buf

  let to_internal = to_string
  let to_external = to_string

  (* Append the encoding of a scalar value to a buffer. *)
  let add_scalar (buf : Buffer.t) (scalar : int) : unit =
    if scalar < 0x80 then Buffer.add_char buf (Char.unsafe_chr scalar)
    else Buffer.add_utf_8_uchar buf (Uchar.unsafe_of_int scalar)
end
