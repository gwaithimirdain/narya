(* Character parsers over a complete UTF-8 string, with the semantics of fmlib-parse's Ucharacter.Make_utf8 (see README.md).  A parser is a function on a mutable state that either returns a value or raises Fail.Fail. *)

open Fail

module Make_utf8 (User : ANY) (Final : ANY) (Semantic : ANY) = struct
  type state = {
    src : string;
    len : int;
    (* Byte index of the next character; len + 1 once the end has been consumed. *)
    mutable i : int;
    (* The current position, unpacked.  It can differ from i, since fmlib advances positions in a peculiar way over invalid UTF-8. *)
    mutable line : int;
    mutable bol : int;
    mutable bcol : int;
    mutable cor : int;
    mutable user : User.t;
    mutable semantic : Semantic.t option;
    (* Scratch space for the decoder. *)
    dec : int array;
  }

  type 'a t = state -> 'a

  let init (src : string) (user : User.t) : state =
    {
      src;
      len = String.length src;
      i = 0;
      line = 0;
      bol = 0;
      bcol = 0;
      cor = 0;
      user;
      semantic = None;
      dec = [| 0; 0 |];
    }

  let current_position (st : state) : Position.t =
    { line = st.line; byte_bol = st.bol; byte_col = st.bcol; correction = st.cor }

  let has_consumed_end (st : state) : bool = st.i > st.len

  (* Run a parser at the current point.  None means it failed; then the position is where it failed. *)
  let run (st : state) (user : User.t) (p : 'a t) : 'a option =
    st.user <- user;
    st.semantic <- None;
    match p st with
    | a -> Some a
    | exception Fail -> None

  let syntax_fail (st : state) : 'a =
    st.semantic <- None;
    raise_notrace Fail

  (* Monad *)

  let return (a : 'a) : 'a t = fun _ -> a
  let succeed = return
  let[@inline] ( >>= ) (p : 'a t) (f : 'a -> 'b t) : 'b t = fun st -> f (p st) st
  let ( let* ) = ( >>= )
  let[@inline] map (f : 'a -> 'b) (p : 'a t) : 'b t = fun st -> f (p st)

  let fail (e : Semantic.t) : 'a t =
   fun st ->
    st.semantic <- Some e;
    raise_notrace Fail

  let unexpected (_ : string) : 'a t = syntax_fail
  let no_expectations (p : 'a t) : 'a t = p
  let get : User.t t = fun st -> st.user
  let set (user : User.t) : unit t = fun st -> st.user <- user
  let update (f : User.t -> User.t) : unit t = fun st -> st.user <- f st.user
  let position : Position.t t = current_position

  (* Alternatives and backtracking *)

  (* Try p; if it fails without consuming, try q.  If p does not consume, its changes to the state are undone, even if it succeeds. *)
  let ( </> ) (p : 'a t) (q : 'a t) : 'a t =
   fun st ->
    let i0 = st.i and u0 = st.user in
    match p st with
    | a ->
        if st.i = i0 then st.user <- u0;
        a
    | exception Fail when st.i = i0 ->
        st.user <- u0;
        q st

  let backtrack (p : 'a t) (_ : string) : 'a t =
   fun st ->
    let i0 = st.i and u0 = st.user in
    let line = st.line and bol = st.bol and bcol = st.bcol and cor = st.cor in
    try p st
    with Fail ->
      st.i <- i0;
      st.user <- u0;
      st.line <- line;
      st.bol <- bol;
      st.bcol <- bcol;
      st.cor <- cor;
      syntax_fail st

  let followed_by (p : 'a t) (_ : string) : 'a t =
   fun st ->
    let i0 = st.i and u0 = st.user in
    let line = st.line and bol = st.bol and bcol = st.bcol and cor = st.cor in
    let restore () =
      st.i <- i0;
      st.user <- u0;
      st.line <- line;
      st.bol <- bol;
      st.bcol <- bcol;
      st.cor <- cor in
    match p st with
    | a ->
        restore ();
        a
    | exception Fail ->
        restore ();
        syntax_fail st

  let optional (p : 'a t) : 'a option t =
   fun st ->
    let i0 = st.i and u0 = st.user in
    match p st with
    | a ->
        if st.i = i0 then st.user <- u0;
        Some a
    | exception Fail when st.i = i0 ->
        st.user <- u0;
        None

  let zero_or_more_fold_left (start : 'r) (f : 'r -> 'a -> 'r t) (p : 'a t) : 'r t =
   fun st ->
    let rec loop r =
      let i0 = st.i and u0 = st.user in
      match f r (p st) st with
      | r -> loop r
      | exception Fail when st.i = i0 ->
          st.user <- u0;
          r in
    loop start

  let zero_or_more (p : 'a t) : 'a list t =
   fun st ->
    let rec loop acc =
      let i0 = st.i and u0 = st.user in
      match p st with
      | a -> loop (a :: acc)
      | exception Fail when st.i = i0 ->
          st.user <- u0;
          List.rev acc in
    loop []

  let one_or_more (p : 'a t) : ('a * 'a list) t =
   fun st ->
    let x = p st in
    (x, zero_or_more p st)

  let one_or_more_fold_left (first : 'a -> 'r t) (f : 'r -> 'a -> 'r t) (p : 'a t) : 'r t =
   fun st ->
    let r = first (p st) st in
    zero_or_more_fold_left r f p st

  let skip_zero_or_more (p : 'a t) : int t = zero_or_more_fold_left 0 (fun n _ _ -> n + 1) p

  let skip_one_or_more (p : 'a t) : int t =
   fun st ->
    let _ = p st in
    skip_zero_or_more p st + 1

  let parenthesized (mk : 'l -> 'a -> 'r -> 'b t) (lpar : 'l t) (p : unit -> 'a t)
      (rpar : 'l -> 'r t) : 'b t =
   fun st ->
    let lp = lpar st in
    let a = p () st in
    let rp = rpar lp st in
    mk lp a rp st

  let located (p : 'a t) : (Position.range * 'a) t =
   fun st ->
    let p1 = current_position st in
    let a = p st in
    ((p1, current_position st), a)

  let expect_end (a : 'a) : 'a t =
   fun st ->
    if st.i = st.len then (
      st.i <- st.len + 1;
      a)
    else syntax_fail st

  (* Characters *)

  let[@inline] advance (st : state) (scalar : int) (bytes : int) (byte_width : int) : unit =
    st.i <- st.i + bytes;
    if scalar = 0x0A then (
      st.line <- st.line + 1;
      st.bol <- st.bol + st.bcol + byte_width;
      st.bcol <- 0;
      st.cor <- 0)
    else (
      st.bcol <- st.bcol + byte_width;
      st.cor <- st.cor + Utf8.width scalar - byte_width)

  let ucharp (f : Uchar.t -> bool) (_ : string) : Uchar.t t =
   fun st ->
    let i = st.i in
    if i >= st.len then syntax_fail st
    else
      let c = Char.code (String.unsafe_get st.src i) in
      if c < 0x80 then
        let u = Uchar.unsafe_of_int c in
        if f u then (
          advance st c 1 1;
          u)
        else syntax_fail st
      else
        let v = Utf8.decode st.src i st.dec in
        let u = Uchar.unsafe_of_int v in
        if f u then (
          advance st v st.dec.(0) st.dec.(1);
          u)
        else syntax_fail st

  let uchar (expected : Uchar.t) : Uchar.t t = ucharp (Uchar.equal expected) ""

  let charp (f : char -> bool) (e : string) : char t =
    map Uchar.to_char
      (ucharp
         (fun u ->
           let i = Uchar.to_int u in
           i < 128 && f (Char.unsafe_chr i))
         e)

  let char (expected : char) : char t =
    let u = Uchar.of_char expected in
    fun st ->
      let _ = uchar u st in
      expected

  let string (str : string) : string t =
   fun st ->
    String.iter (fun c -> ignore (char c st)) str;
    str

  let one_of_chars (str : string) (e : string) : char t = charp (fun c -> String.contains str c) e

  let word (first : char -> bool) (inner : char -> bool) (e : string) : string t =
   fun st ->
    let c0 = charp first e st in
    let buf = Buffer.create 16 in
    Buffer.add_char buf c0;
    let _ = zero_or_more_fold_left () (fun () c _ -> Buffer.add_char buf c) (charp inner e) st in
    Buffer.contents buf

  let uword (first : Uchar.t -> bool) (inner : Uchar.t -> bool) (e : string) : string t =
   fun st ->
    let c0 = ucharp first e st in
    let buf = Buffer.create 16 in
    Buffer.add_string buf (Utf8.Encoder.to_internal c0);
    let _ =
      zero_or_more_fold_left ()
        (fun () c _ -> Buffer.add_string buf (Utf8.Encoder.to_internal c))
        (ucharp inner e) st in
    Buffer.contents buf
end
