(* Direct-style character parsing over a complete UTF-8 string.  A lexer is written as ordinary functions on the state that look at the next character with "peek", consume it with "junk", and fail with "syntax_fail" (raising Fail.Fail), using "backtrack" to undo a partial attempt.  The input must be valid UTF-8: "peek" raises Invalid_utf8 when it reaches a byte sequence that isn't. *)

open Fail

(* The range of a maximal invalid subsequence of the input (in the sense of the Unicode standard), at which "peek" stopped. *)
exception Invalid_utf8 of Position.range

type state = {
  src : string;
  len : int;
  (* Byte index of the next character; len + 1 once the end has been consumed. *)
  mutable i : int;
  (* The current line, and the byte index of its start. *)
  mutable line : int;
  mutable bol : int;
  (* The length in bytes of the character last returned by "peek". *)
  mutable peeked : int;
}

let init (src : string) : state =
  { src; len = String.length src; i = 0; line = 0; bol = 0; peeked = 0 }

let position_at (st : state) (i : int) : Position.t =
  { line = st.line; byte_bol = st.bol; byte_col = i - st.bol }

(* After the end has been consumed, the index is one past the end of the input, but the position is at its end. *)
let current_position (st : state) : Position.t = position_at st (if st.i > st.len then st.len else st.i)
let index (st : state) : int = st.i
let has_consumed_end (st : state) : bool = st.i > st.len

(* Run a lexer at the current point.  None means it failed; then the current position is where it failed. *)
let run (st : state) (p : state -> 'a) : 'a option =
  match p st with
  | a -> Some a
  | exception Fail -> None

let syntax_fail (_ : state) : 'a = raise_notrace Fail

(* The next character as a scalar value, or -1 at the end of the input. *)
let[@inline] peek (st : state) : int =
  let i = st.i in
  if i >= st.len then -1
  else
    let c = Char.code (String.unsafe_get st.src i) in
    if c < 0x80 then (
      st.peeked <- 1;
      c)
    else
      let d = String.get_utf_8_uchar st.src i in
      let n = Uchar.utf_decode_length d in
      if Uchar.utf_decode_is_valid d then (
        st.peeked <- n;
        Uchar.to_int (Uchar.utf_decode_uchar d))
      else raise (Invalid_utf8 (position_at st i, position_at st (i + n)))

(* The range of the character just returned by "peek". *)
let peeked_range (st : state) : Position.range =
  (current_position st, position_at st (st.i + st.peeked))

(* Consume the character just returned by "peek", whose scalar value is v. *)
let[@inline] junk (st : state) (v : int) : unit =
  st.i <- st.i + st.peeked;
  if v = 0x0A then (
    st.line <- st.line + 1;
    st.bol <- st.i)

(* The text between two byte indices. *)
let text (st : state) (start : int) (stop : int) : string = String.sub st.src start (stop - start)

(* Run p; if it fails, restore the state and fail without having consumed anything. *)
let backtrack (p : state -> 'a) (st : state) : 'a =
  let i = st.i and line = st.line and bol = st.bol in
  try p st
  with Fail ->
    st.i <- i;
    st.line <- line;
    st.bol <- bol;
    raise_notrace Fail

(* Consume the end of the input, or fail if it hasn't been reached. *)
let expect_end (a : 'a) (st : state) : 'a =
  if st.i = st.len then (
    st.i <- st.len + 1;
    a)
  else raise_notrace Fail
