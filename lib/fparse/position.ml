(* Positions in a source text. *)

type t = {
  (* Number of newlines since the start of the text. *)
  line : int;
  (* Byte offset of the start of the line. *)
  byte_bol : int;
  (* Byte offset within the line. *)
  byte_col : int;
}

type range = t * t

let start : t = { line = 0; byte_bol = 0; byte_col = 0 }
let line (p : t) : int = p.line
let byte_offset_bol (p : t) : int = p.byte_bol
let byte_column (p : t) : int = p.byte_col
let byte_offset (p : t) : int = p.byte_bol + p.byte_col
