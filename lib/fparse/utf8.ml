(* UTF-8 encoding and decoding, reproducing fmlib-parse's behaviour exactly (including on invalid input), since it determines both the strings the lexer builds and the positions it reports. *)

module Encoder = struct
  type t = Uchar.t

  (* Like fmlib, scalars below 0x8F (not 0x80) are written as a single byte. *)
  let to_string (scalar : int) : string =
    if scalar < 0x8F then String.make 1 (Char.unsafe_chr scalar)
    else if scalar lsr 11 = 0 then (
      let b = Bytes.create 2 in
      Bytes.unsafe_set b 0 (Char.unsafe_chr (0xC0 lor (scalar lsr 6)));
      Bytes.unsafe_set b 1 (Char.unsafe_chr (0x80 lor (scalar land 0x3F)));
      Bytes.unsafe_to_string b)
    else if scalar lsr 16 = 0 then (
      let b = Bytes.create 3 in
      Bytes.unsafe_set b 0 (Char.unsafe_chr (0xE0 lor (scalar lsr 12)));
      Bytes.unsafe_set b 1 (Char.unsafe_chr (0x80 lor ((scalar lsr 6) land 0x3F)));
      Bytes.unsafe_set b 2 (Char.unsafe_chr (0x80 lor (scalar land 0x3F)));
      Bytes.unsafe_to_string b)
    else
      let b = Bytes.create 4 in
      Bytes.unsafe_set b 0 (Char.unsafe_chr (0xF0 lor (scalar lsr 18)));
      Bytes.unsafe_set b 1 (Char.unsafe_chr (0x80 lor ((scalar lsr 12) land 0x3F)));
      Bytes.unsafe_set b 2 (Char.unsafe_chr (0x80 lor ((scalar lsr 6) land 0x3F)));
      Bytes.unsafe_set b 3 (Char.unsafe_chr (0x80 lor (scalar land 0x3F)));
      Bytes.unsafe_to_string b

  let to_internal (uc : t) : string = to_string (Uchar.to_int uc)
  let to_external = to_internal
end

(* The display width that fmlib assigns to a character. *)
let width (scalar : int) : int =
  if scalar = 0x09 then 4
  else if scalar < 0x20 then 0
  else
    match scalar with
    | 0x200B | 0xFEFF | 0x200C | 0x200D -> 0
    | _ -> 1

let rep = Uchar.to_int Uchar.rep
let valid v = if Uchar.is_valid v then v else rep

(* Decode the character starting at byte [i < String.length s], which is not ASCII.  Returns the scalar (U+FFFD for errors), and writes into [out] the number of bytes of [s] it occupies ([out.(0)]) and the byte width by which fmlib advances the position ([out.(1)]).  These differ in one case: when a multibyte sequence is interrupted by a byte that is not a continuation byte, fmlib's decoder swallows that byte and reports a byte width of one more than the declared length of the sequence.  An incomplete sequence at the end of the input is delivered with the partial value it has accumulated. *)
let decode (s : string) (i : int) (out : int array) : int =
  let len = String.length s in
  let c = Char.code (String.unsafe_get s i) in
  let missing, v =
    if c lsr 5 = 0b110 then (1, c land 0x1F)
    else if c lsr 4 = 0b1110 then (2, c land 0x0F)
    else if c lsr 3 = 0b11110 then (3, c land 0x07)
    else (-1, 0) in
  if missing < 0 then (
    out.(0) <- 1;
    out.(1) <- 1;
    rep)
  else
    let length = missing + 1 in
    let rec go j v missing =
      if missing = 0 then (
        out.(0) <- length;
        out.(1) <- length;
        valid v)
      else if j >= len then (
        out.(0) <- j - i;
        out.(1) <- j - i;
        valid v)
      else
        let d = Char.code (String.unsafe_get s j) in
        if d lsr 6 = 0b10 then go (j + 1) ((v lsl 6) + (d land 0x3F)) (missing - 1)
        else (
          out.(0) <- j - i + 1;
          out.(1) <- length + 1;
          rep) in
    go (i + 1) v missing
