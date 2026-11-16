(* A stream of located tokens, produced on demand by a lexer and buffered so that token parsers can look ahead and backtrack.  Successive runs of token parsers on the same stream (e.g. one per command) continue where the previous run stopped. *)

type 'tok next =
  (* The lexer produced a token. *)
  | Token of (Position.range * 'tok)
  (* The lexer reached (and consumed) the end of the input, at the given position. *)
  | End of Position.t
  (* The lexer failed, at the given position. *)
  | Failed of Position.t

type status = Open | Ended of Position.t | Lexer_failed of Position.t

type 'tok t = {
  (* The buffered tokens are toks.(0) .. toks.(ntoks - 1). *)
  mutable toks : (Position.range * 'tok) array;
  mutable ntoks : int;
  mutable status : status;
  next : unit -> 'tok next;
  (* The index at which the next run of a parser starts.  It is ntoks + 1 if the end of input has been consumed. *)
  mutable index : int;
}

(* Raised when a parser asks for a token that the lexer failed to produce.  It is not a parse failure: no alternative is tried, and the whole parse fails. *)
exception Lex_failure of Position.t

let make (next : unit -> 'tok next) : 'tok t =
  { toks = [||]; ntoks = 0; status = Open; next; index = 0 }

let push (ts : 'tok t) (x : Position.range * 'tok) : unit =
  let n = ts.ntoks in
  if n = Array.length ts.toks then (
    let toks = Array.make (max 16 (2 * n)) x in
    Array.blit ts.toks 0 toks 0 n;
    ts.toks <- toks);
  Array.unsafe_set ts.toks n x;
  ts.ntoks <- n + 1

(* Try to lex one more token.  Returns true if one was added, false at end of input. *)
let fill (ts : 'tok t) : bool =
  match ts.status with
  | Open -> (
      match ts.next () with
      | Token x ->
          push ts x;
          true
      | End pos ->
          ts.status <- Ended pos;
          false
      | Failed pos ->
          ts.status <- Lexer_failed pos;
          raise (Lex_failure pos))
  | Ended _ -> false
  | Lexer_failed pos -> raise (Lex_failure pos)

(* Forget the tokens before [index], which no later run can see. *)
let compact (ts : 'tok t) : unit =
  let k = if ts.index < ts.ntoks then ts.index else ts.ntoks in
  if k > 0 then (
    Array.blit ts.toks k ts.toks 0 (ts.ntoks - k);
    (* Don't keep the forgotten tokens alive. *)
    if ts.ntoks - k > 0 then Array.fill ts.toks (ts.ntoks - k) k ts.toks.(0) else ts.toks <- [||];
    ts.ntoks <- ts.ntoks - k;
    ts.index <- ts.index - k)

let has_consumed_end (ts : 'tok t) : bool =
  match ts.status with
  | Ended _ -> ts.index > ts.ntoks
  | _ -> false
