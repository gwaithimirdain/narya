(* Token parsers over a Tokens.t stream (see README.md).  A parser is a function on a mutable state that either returns a value or raises Fail.Fail. *)

open Fail

module Make (User : ANY) (Token : ANY) (Final : ANY) (Semantic : ANY) = struct
  type state = {
    tokens : Token.t Tokens.t;
    (* Index of the next token in tokens.toks; tokens.ntoks + 1 once the end has been consumed. *)
    mutable index : int;
    (* The index at which this run started. *)
    start : int;
    mutable user : User.t;
    (* The semantic error of the most recent failure, if it was semantic. *)
    mutable semantic : Semantic.t option;
  }

  type 'a t = state -> 'a

  let[@inline] imin (a : int) (b : int) : int = if a < b then a else b

  (* The end of the last token among the first k of the stream, or Position.start if none of them belong to this run. *)
  let pos2_after (st : state) (k : int) : Position.t =
    if k > st.start then snd (fst (Array.unsafe_get st.tokens.toks (k - 1))) else Position.start

  let[@inline] set_user (st : state) (u : User.t) : unit = if st.user != u then st.user <- u

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

  (* Run a parser on a token stream, starting where the previous run on it stopped, with a fresh state.  To require the parser to reach the end of the input, end it with "expect_end". *)
  let run (tokens : Token.t Tokens.t) (user : User.t) (p : 'a t) : 'a outcome =
    Tokens.compact tokens;
    let st = { tokens; index = tokens.index; start = tokens.index; user; semantic = None } in
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

  (* Try p; if it fails without consuming, undo its changes to the user state and try q. *)
  let ( </> ) (p : 'a t) (q : 'a t) : 'a t =
   fun st ->
    let i0 = st.index and u0 = st.user in
    match p st with
    | a -> a
    | exception Fail when st.index = i0 ->
        set_user st u0;
        q st

  let backtrack (p : 'a t) (_ : string) : 'a t =
   fun st ->
    let i0 = st.index and u0 = st.user in
    try p st
    with Fail ->
      st.index <- i0;
      set_user st u0;
      syntax_fail st

  let followed_by (p : 'a t) (_ : string) : 'a t =
   fun st ->
    let i0 = st.index and u0 = st.user in
    let restore () =
      st.index <- i0;
      set_user st u0 in
    match p st with
    | a ->
        restore ();
        a
    | exception Fail ->
        restore ();
        syntax_fail st

  let optional (p : 'a t) : 'a option t =
   fun st ->
    let i0 = st.index and u0 = st.user in
    match p st with
    | a -> Some a
    | exception Fail when st.index = i0 ->
        set_user st u0;
        None

  let zero_or_more_fold_left (start : 'r) (f : 'r -> 'a -> 'r t) (p : 'a t) : 'r t =
   fun st ->
    let rec loop r =
      let i0 = st.index and u0 = st.user in
      match f r (p st) st with
      | r -> loop r
      | exception Fail when st.index = i0 ->
          set_user st u0;
          r in
    loop start

  let zero_or_more (p : 'a t) : 'a list t =
   fun st ->
    let rec loop acc =
      let i0 = st.index and u0 = st.user in
      match p st with
      | a -> loop (a :: acc)
      | exception Fail when st.index = i0 ->
          set_user st u0;
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
        let rng, tok = Array.unsafe_get ts.toks i in
        match f st.user rng tok with
        | Some (a, user) ->
            set_user st user;
            st.index <- i + 1;
            a
        | None -> syntax_fail st
      else if i = ts.ntoks && Tokens.fill ts then go st
      else syntax_fail st in
    go

  (* Consume the end of input.  This does not count as consuming a token for "located". *)
  let expect_end (a : 'a) : 'a t =
   fun st ->
    let ts = st.tokens in
    if st.index < ts.ntoks || Tokens.fill ts then syntax_fail st
    else (
      st.index <- ts.ntoks + 1;
      a)

  (* The range from the start of the first token consumed by p to the end of the last.  If p consumes no tokens, it is the zero-width range at the end of the last token consumed before it (or at Position.start, if there is none in this run). *)
  let located (p : 'a t) : (Position.range * 'a) t =
   fun st ->
    let i0 = st.index in
    let a = p st in
    let k = imin st.index st.tokens.ntoks in
    if k > i0 then ((fst (fst (Array.unsafe_get st.tokens.toks i0)), pos2_after st k), a)
    else
      let p = pos2_after st k in
      ((p, p), a)
end
