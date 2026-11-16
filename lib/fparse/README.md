# fparse: a direct-style replacement for fmlib-parse

This is a small parsing library replacing the parts of fmlib-parse 0.6.2
that Narya used.  Fmlib is an incremental *push* parser: a
continuation-passing state monad over an immutable buffer record that is copied
at every step, with expectation tracking for error messages.  Narya never feeds
input incrementally and never displays expectations, and parsing costs ~27% of
run time and ~45% of allocation on large developments.  This library instead
represents a parser as a function `state -> 'a` over a mutable state that fails
by raising a private exception, and pulls tokens from a lazily-filled token
array.

The modules are `Position` and `Utf8` (same values as fmlib's, quirks
included), `Ucharacter.Make_utf8` (character layer), `Tokens` (the on-demand
token stream), and `Token_parser.Make` (token layer, with the driver `run`).
`Lexer.tokens` in lib/parser builds a token stream from a source string.

This file records the exact behaviour of fmlib (read from
`~/.opam/default/.opam-switch/sources/fmlib_parse.0.6.2/src/parse/`) that Narya
can observe, and which the replacement must therefore reproduce.  Anything not
listed here is either unused by Narya or invisible to it.

## What Narya uses

Combinators are used only in `lib/parser/lexer.ml` (character layer, via
`Ucharacter.Make_utf8`), `lib/parser/parse.ml` and `lib/parser/command.ml`
(token layer, via `Token_parser.Make` inside `Parse.Combinators`; command.ml
does `open C.Basic`), plus `test/testutil/lex.ml`.  Other modules use only
`Position` (range.ml) and `Utf8.Encoder.to_internal` (lexer.ml).

- Both layers: `return`, `>>=`/`let*`, `map`, `</>`, `backtrack`, `get`, `set`,
  `optional`, `zero_or_more`, `zero_or_more_fold_left`, `one_or_more`,
  `one_or_more_fold_left`, `skip_one_or_more`, `parenthesized`, `expect_end`,
  `located`.
- Token layer only: `step`, `followed_by` (parse.ml:229, around a `step`),
  `fail` (semantic errors), `succeed`.
- Character layer only: `ucharp`, `uword`, `word`, `one_of_chars`,
  `unexpected` (in `Lexer.key`, inside `backtrack`), `no_expectations`.
  Lexer.ml already redefines `uchar`, `char`, `string` in terms of `ucharp`.
- Not used anywhere: `update`, indentation (`indent`, `align`, `left_align`, `detach`;
  so fmlib's `check_position` always succeeds, since the initial lower bound
  is column 0), `<?>`, `not_followed_by`, `state_around`, `get_and_update`,
  `map_and_update`, `choices`, `counted`, `operator_expression`,
  `one_or_more_separated`, `clear_last_expectation`.  `failed_expectations` is
  used only by `test/testutil/lex.ml` (`nolex`, one assertion in
  `test/parser/lexer.ml:162`), which can be changed.

## Core semantics (fmlib `Generic` + `Buffer`)

The two most surprising rules below (the `</>` state rollback on success and
the `located` quirk) were confirmed with a small test program against fmlib
0.6.2 on 2026-11-16.

A parser either succeeds with a value or fails.  Each run tracks whether it
*consumed* input; consuming the end of input counts.  With an index into the
input, "p consumed" is exactly "the index after p is greater than before p",
because the only operations that move the index backwards (`backtrack` on
failure, `followed_by`) restore it to their own starting point.

- `return a`: succeed, no effect.  `succeed a`: same (it only clears error
  messages).  `map`, `>>=`: as usual; a failure of `p` in `p >>= f` propagates.
- `p </> q`: run `p`.  If `p` failed **without consuming**, run `q`.
  Otherwise the result of `p` is the result, success or failure.
  **State rollback:** whenever `p` did not consume, *on success as well as on
  failure*, the parser state is reset to its value before `p`
  (`Buffer.end_new_consumer`: `state = if b.has_consumed then b.state else
  b0.state`).  So `set x </> q` that succeeds without consuming discards the
  `set`.  "State" here is the whole fmlib state record: in the token layer the
  user state *and* the location-tracking fields (`pos1`, `consumed`; see
  `located` below); in the character layer the user state (positions change
  only by consumption).
- `backtrack p _`: run `p`.  On success, keep everything.  On failure, restore
  the index and the entire state to their values before `p`, and fail
  *without having consumed* (so an enclosing `</>` tries its alternative).
- `followed_by p _`: run `p`, then restore the index and the entire state to
  their values before `p` in either case; on success return `p`'s value, on
  failure fail without having consumed.  (fmlib asserts if `p` consumed the
  end of input and failed; irrelevant here.)
- `optional p` = `(p >>= fun a -> return (Some a)) </> return None`.
- `zero_or_more_fold_left start f p`: `let rec many r = (let* a = p in let* r
  = f r a in many r) </> return r in many start`.  The `</>` around each
  iteration includes all later iterations, but since a later iteration can only
  run after `p` succeeded, and a `p` that succeeds without consuming loops
  forever in fmlib too, a loop is equivalent: run `p; f`; if that fails
  without consuming, roll back the state to the start of this iteration and
  return the accumulator; if it fails after consuming, fail.
  `zero_or_more p` is the same, collecting a list in order (fmlib's
  `zero_or_more_fold_right` makes the same choices).  `one_or_more p`
  = `p` then `zero_or_more p`, returning `(x, xs)`.
  `one_or_more_fold_left first f p` = `p >>= first`, then
  `zero_or_more_fold_left`.  `skip_one_or_more p` = count of iterations.
- `parenthesized mk lpar p rpar` = `let* lp = lpar in let* a = p () in let* rp
  = rpar lp in mk lp a rp`.
- `get`, `set`, `update`: read/write the *user* state.
- `fail e`: fail with semantic error `e`, without consuming.
  `unexpected _`: fail with a syntax error, without consuming.
- `no_expectations p` = `p` (it only manipulates error messages).
- `expect_end a`: if the next item is the end of input, consume it and return
  `a`, **without touching the state** (so the token layer's location fields
  are not updated: a `located` around it covers no token).  Otherwise fail
  without consuming.

### Errors

Narya distinguishes only "syntax failure" (reported as `Parse_error "invalid
syntax"` at a location) from "semantic failure" (`SemanticError.t`, carrying
its own location).  The error at the final failure is determined by the
*last failure origin*: `fail e` makes it semantic; every other origin
(`step` rejecting, `expect_end` rejecting, `unexpected`, `backtrack` failing,
`followed_by` failing) makes it syntactic, even if a semantic error was
pending (`Error.add_expected` on a `Semantic` error yields `Syntax`).
Propagating a failure through `>>=`, `located`, `map`, or a consumed `</>`
leaves it unchanged.  Implementation: a mutable `semantic` field set by `fail`
and cleared by every other raise site.

## Token layer (`Token_parser`)

State: user state, `pos1`, `pos2` (fmlib `Position.t`), `consumed : bool`
(indentation is unused).  A new token parser starts with `pos1 = pos2 =
Position.start`, `consumed = false`; this happens for *every command*
(`make_next`), not just at the start of a file.

- `step _ f`: if the next item is a token `((p1, p2), tok)`, call `f user
  (p1, p2) tok`.  `Some (a, user')` consumes the token, sets the user state to
  `user'`, and updates the location fields with `next`: `pos1 := if consumed
  then pos1 else p1; pos2 := p2; consumed := true`.  `None`, or the end of
  input, fails without consuming (syntax).
- `located p`: save the state `s0`; set `pos1 := pos2; consumed := false`; run
  `p`; the result range is `(pos1, pos2)` *at this moment*; then, if
  `s0.consumed`, set `pos1 := s0.pos1` (leaving `consumed` as it is now).  So:
  - if `p` consumed tokens, the range runs from the start of its first token to
    the end of its last;
  - if `p` consumed nothing, the range is zero-width at the end of the last
    token consumed before (or `Position.start` in a fresh parser);
  - fmlib quirk to reproduce: if an enclosing `located` had already consumed and
    this `p` consumed nothing, `consumed` is left `false`, so the enclosing
    range's start is overwritten by the next token consumed — unless a
    surrounding non-consuming `</>` rolls the state back first.
- `expect_end a`: as above.

## Character layer (`Ucharacter.Make_utf8`)

State: user state and a `Position.t` (line, byte offset of line start, byte
column, column correction).

- Decoding follows `Fmlib_parse.Utf8.Decoder` exactly, including its quirks:
  an invalid lead byte is an error of length 1; a lead byte followed by a
  non-continuation byte is an error that *includes* that byte; an error decodes
  as `Uchar.rep`; an incomplete sequence at end of input is delivered as a
  character whose value is the partial scalar (if valid) and whose byte width
  is the number of bytes seen.  Overlong forms are not rejected.  ASCII bytes
  can take a fast path.
- `ucharp f _`: at a character `c`, if `f (uchar c)` consume it and return the
  `Uchar.t`; otherwise, or at end, fail without consuming.  Consuming updates
  the position by `Position.newline (byte_width c)` if `c` is LF (only LF), and
  otherwise `Position.advance (byte_width c) (width c)`, where `width` is 4 for
  tab, 0 for other controls below space and for U+200B/U+200C/U+200D/U+FEFF,
  and 1 otherwise.  (Narya never reads columns, but `Range.convert` compares
  positions with `=`, so keep the correction exact.)
- `word first inner _` / `uword`: one char satisfying `first`, then as many
  satisfying `inner` as possible; returns the string (for `uword`, the
  internal UTF-8 encoding of the decoded characters, so invalid bytes become
  U+FFFD).  `one_of_chars s _` = an ASCII char in `s`.
- `located p` = positions before and after `p` (no quirks).
- `expect_end a`: consume the end, position unchanged.

## Lexer driver (`Parse_with_lexer` + `Lexer.Parser`)

- The first token is produced by `Lexer.bof` from `Position.start` (leading
  whitespace and comments, a zero-width `Bof`).  Every later token is produced
  by `Lexer.token`, with the lexer's user state reset to `` `None `` and the
  position and input index continuing where the previous token stopped
  (`restart` = `make_partial (position lex) `None token |> transfer_lookahead
  lex`; fmlib's lookahead characters are just the characters at and after the
  index).  Each token carries the whitespace *after* it.
- `Lexer.token` ends with `located (expect_end (Eof, []))`.  When the lexer
  succeeds by consuming the end of input, that `Eof` token is **never** given
  to the token parser (`check_token` only pushes tokens when the lexer has not
  consumed the end); instead the token parser sees the end of input.  So the
  token stream is `Bof, t1, ..., tn, end`.
- Tokens are lexed on demand: fmlib feeds characters only while the token
  parser is waiting for a token, and the lexer cannot finish a token without
  seeing the character after it.  So a pull design that lexes token *i* when
  the parser first examines index *i* lexes the same tokens at the same moments.
  This matters because lexing has effects: `fatal` from `canonicalize`, `emit
  Comment_end_in_string`, `Range.convert` (Range reader effect), and reads of
  `Lexer.Specials.current`; these must keep happening inside the same
  `Range.run` / `Specials.run` and before or after the same command executions.
- A lexer *failure* (e.g. an unterminated block comment or string, or a
  character no token accepts, such as a Unicode tag character) does not fail
  the token parser: fmlib's token parser just waits forever.  It is reported,
  as a syntax failure, only if the token parser asks for that token, and then
  the parse as a whole fails at once: it is **not** a token-layer failure that
  `</>` could catch.  Its range is zero-width at the lexer's position at the
  moment of failure (after any `backtrack` restores).  `Range.convert` turns
  that into an EOF location if it is at the end of input, and otherwise raises
  `Anomaly "zero-width range during parse failure before EOF"` (unchanged
  behaviour).  Tokens lexed before the failure remain usable, and a later
  command parse that asks for the failing token fails the same way.
- A token-layer syntax failure is reported at the range of the first token not
  consumed (the token at the current index after restores), or, if there is
  none because the end of input was rejected, zero-width at the end of input.
- `has_consumed_end` = the token parser consumed the end of input.
- Commands: `Command.Parse.start_parse` runs `located_command` (with
  `make_partial`) on a fresh token parser; `restart_parse` runs it again on a
  fresh token parser (fresh user state `Origin.current ()`, fresh location
  fields) that continues at the current token index with the same lexer.
  `Parse.Term.parse` and `Lexer.single` use `make` (= the parser followed by
  `expect_end`).
- Files are read through `In_channel.open_text` (CRLF translation on Windows),
  and `Range.Data.length` is `In_channel.length`; reading the whole channel
  with `In_channel.input_all` gives the same characters.
- `run_on_string_at` returning the next offset is only needed by the push
  design; a pull design keeps the input and index in the stream.

## Design of the replacement

- `type 'a t = state -> 'a`; failure is `raise_notrace Fail` of an exception
  private to the library.  `</>`, `backtrack`, `followed_by` and the loops
  catch only `Fail`, never Asai's `fatal` or other exceptions (the lexer calls
  `fatal` while parsing), and never the lexer-failure exception.
- Mutable state record.  Token layer: token array (growable, filled on demand
  from the lexer), index, user state, `pos1`, `pos2`, `consumed`, `semantic`.
  Character layer: input string, byte index, current `Position.t` (or its four
  fields), user state.
- `</>` saves the index and the state fields listed above; on return without
  consumption it restores them, then returns or tries `q`.
- Driver: a pull API returning success, syntax failure with a range, or
  semantic failure, replacing `make`/`make_partial`/`make_next`/`run_on_*`/
  `has_*`/`final`/`range` at the call sites listed in
  `memory: fast-parser-plan` (Lexer.Parser, Lexer.single, Parse.ensure_success,
  Parse.Term.parse, Command.Parse.*, test/testutil/lex.ml).
- Since monadic and direct-style parsers then have the same type, Narya's
  code can later be converted file by file (`let* x = p in e` becomes `let x =
  p st in e`).

## Known differences from fmlib

- If a token parser fails without ever having looked at the token at the
  current index (possible only through `fail`/`unexpected`, which Narya does not
  use that way), the reported range is that of the next token, lexed for the
  purpose; fmlib reported the lexer's position part-way into it.
- Consuming the end of input inside `backtrack` or `followed_by` and then
  failing was an assertion failure in fmlib; here it is unconsumed.
- Parsers run on the OCaml stack: deeply nested input nests calls, where
  fmlib's continuations lived on the heap.
