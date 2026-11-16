(* Token parsers over a Tokens.t stream, with the semantics of fmlib-parse's Token_parser.Make (see README.md).  A parser is a function on a mutable state that either returns a value or raises Fail.Fail. *)

open Fail

module Make (User : ANY) (Token : ANY) (Final : ANY) (Semantic : ANY) = struct
  type state = {
    tokens : Token.t Tokens.t;
    (* Index of the next token in tokens.toks; tokens.ntoks + 1 once the end has been consumed. *)
    mutable index : int;
    mutable user : User.t;
    (* Location tracking for "located", as in fmlib: the start of the first token and the end of the last token consumed since the innermost "located" began, and whether any were. *)
    mutable pos1 : Position.t;
    mutable pos2 : Position.t;
    mutable consumed : bool;
    (* The semantic error of the most recent failure, if it was semantic. *)
    mutable semantic : Semantic.t option;
  }

  type 'a t = state -> 'a

  type 'a outcome =
    | Success of 'a
    | Failed_syntax of Position.range
    | Failed_semantic of Semantic.t

  (* The range to report for a syntax failure at the current index: the first token not consumed, or the end of the input. *)
  let failure_range (st : state) : Position.range =
    let ts = st.tokens in
    match if st.index < ts.ntoks || Tokens.fill ts then `Token else `End with
    | `Token -> fst ts.toks.(st.index)
    | `End -> (
        match ts.status with
        | Ended pos -> (pos, pos)
        | Open | Lexer_failed _ -> failwith "Fparse: token stream neither ended nor failed")
    | exception Tokens.Lex_failure pos -> (pos, pos)

  (* Run a parser on a token stream, starting where the previous run on it stopped, with a fresh state.  This is fmlib's "make_partial"; for "make", end the parser with "expect_end". *)
  let run (tokens : Token.t Tokens.t) (user : User.t) (p : 'a t) : 'a outcome =
    Tokens.compact tokens;
    let st =
      {
        tokens;
        index = tokens.index;
        user;
        pos1 = Position.start;
        pos2 = Position.start;
        consumed = false;
        semantic = None;
      } in
    match p st with
    | a ->
        tokens.index <- st.index;
        Success a
    | exception Fail -> (
        match st.semantic with
        | Some e -> Failed_semantic e
        | None -> Failed_syntax (failure_range st))
    | exception Tokens.Lex_failure pos -> Failed_syntax (pos, pos)

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

  (* Alternatives and backtracking *)

  (* Try p; if it fails without consuming, try q.  If p does not consume, its changes to the state (the user state and the location tracking) are undone, even if it succeeds. *)
  let ( </> ) (p : 'a t) (q : 'a t) : 'a t =
   fun st ->
    let i0 = st.index and u0 = st.user and p10 = st.pos1 and c0 = st.consumed in
    match p st with
    | a ->
        if st.index = i0 then (
          st.user <- u0;
          st.pos1 <- p10;
          st.consumed <- c0);
        a
    | exception Fail when st.index = i0 ->
        st.user <- u0;
        st.pos1 <- p10;
        st.consumed <- c0;
        q st

  let backtrack (p : 'a t) (_ : string) : 'a t =
   fun st ->
    let i0 = st.index and u0 = st.user and p10 = st.pos1 and p20 = st.pos2 and c0 = st.consumed in
    try p st
    with Fail ->
      st.index <- i0;
      st.user <- u0;
      st.pos1 <- p10;
      st.pos2 <- p20;
      st.consumed <- c0;
      syntax_fail st

  let followed_by (p : 'a t) (_ : string) : 'a t =
   fun st ->
    let i0 = st.index and u0 = st.user and p10 = st.pos1 and p20 = st.pos2 and c0 = st.consumed in
    let restore () =
      st.index <- i0;
      st.user <- u0;
      st.pos1 <- p10;
      st.pos2 <- p20;
      st.consumed <- c0 in
    match p st with
    | a ->
        restore ();
        a
    | exception Fail ->
        restore ();
        syntax_fail st

  let optional (p : 'a t) : 'a option t =
   fun st ->
    let i0 = st.index and u0 = st.user and p10 = st.pos1 and c0 = st.consumed in
    match p st with
    | a ->
        if st.index = i0 then (
          st.user <- u0;
          st.pos1 <- p10;
          st.consumed <- c0);
        Some a
    | exception Fail when st.index = i0 ->
        st.user <- u0;
        st.pos1 <- p10;
        st.consumed <- c0;
        None

  let zero_or_more_fold_left (start : 'r) (f : 'r -> 'a -> 'r t) (p : 'a t) : 'r t =
   fun st ->
    let rec loop r =
      let i0 = st.index and u0 = st.user and p10 = st.pos1 and c0 = st.consumed in
      match f r (p st) st with
      | r -> loop r
      | exception Fail when st.index = i0 ->
          st.user <- u0;
          st.pos1 <- p10;
          st.consumed <- c0;
          r in
    loop start

  let zero_or_more (p : 'a t) : 'a list t =
   fun st ->
    let rec loop acc =
      let i0 = st.index and u0 = st.user and p10 = st.pos1 and c0 = st.consumed in
      match p st with
      | a -> loop (a :: acc)
      | exception Fail when st.index = i0 ->
          st.user <- u0;
          st.pos1 <- p10;
          st.consumed <- c0;
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

  (* Tokens *)

  (* Consume the next token if f accepts it, passing f the user state and the token's range. *)
  let step (_ : string) (f : User.t -> Position.range -> Token.t -> ('a * User.t) option) : 'a t =
    let rec go st =
      let ts = st.tokens in
      let i = st.index in
      if i < ts.ntoks then
        let ((p1, p2) as rng), tok = Array.unsafe_get ts.toks i in
        match f st.user rng tok with
        | Some (a, user) ->
            st.user <- user;
            if not st.consumed then (
              st.pos1 <- p1;
              st.consumed <- true);
            st.pos2 <- p2;
            st.index <- i + 1;
            a
        | None -> syntax_fail st
      else if i = ts.ntoks && Tokens.fill ts then go st
      else syntax_fail st in
    go

  (* Consume the end of input.  Like fmlib, this does not count as consuming a token for "located". *)
  let expect_end (a : 'a) : 'a t =
   fun st ->
    let ts = st.tokens in
    if st.index < ts.ntoks || Tokens.fill ts then syntax_fail st
    else (
      st.index <- ts.ntoks + 1;
      a)

  (* The range of the tokens consumed by p, with fmlib's conventions (see README.md). *)
  let located (p : 'a t) : (Position.range * 'a) t =
   fun st ->
    let c0 = st.consumed and p10 = st.pos1 in
    st.pos1 <- st.pos2;
    st.consumed <- false;
    let a = p st in
    let rng = (st.pos1, st.pos2) in
    if c0 then st.pos1 <- p10;
    (rng, a)
end
