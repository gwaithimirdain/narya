# fparse: Narya's parsing library

This is a small parsing library that replaced fmlib-parse 0.6.2 in Narya.
Fmlib is an incremental *push* parser: a continuation-passing state monad over
an immutable buffer record copied at every step, with expectation tracking for
error messages.  Narya never feeds input incrementally and never displays
expectations, and that machinery cost ~27% of run time and ~45% of allocation
on large developments.  Here a parser is a function `state -> 'a` on a mutable
state that fails by raising a private exception, and token parsers pull tokens
from a stream that the lexer fills on demand.

Modules:

- `Position`: a position (line, byte offset of the line start, byte column)
  and ranges.
- `Utf8`: UTF-8 encoding.
- `Fail`: the private failure exception, and the `ANY` signature.
- `Ucharacter`: direct-style primitives for writing a lexer over a complete
  UTF-8 string.
- `Tokens`: the on-demand token stream.
- `Token_parser.Make`: monadic token-parser combinators and the driver `run`.

`Lexer.tokens` in lib/parser builds a token stream from a source string; the
lexer itself is written directly with `Ucharacter`.

## Character layer (`Ucharacter`)

A lexer is a set of ordinary functions on a `state`: `peek` returns the next
character as a scalar value (or -1 at the end of input), `junk` consumes the
character just peeked at, `text` extracts the text between two byte indices,
`syntax_fail` fails, `backtrack p` runs `p` and on failure restores the state
and fails without having consumed, `expect_end` consumes the end of input, and
`run` runs a lexer at the current point (returning `None` on failure, leaving
the current position where it failed).

The input must be valid UTF-8 (strict: no overlong encodings or surrogates).
When `peek` reaches an invalid sequence it raises `Invalid_utf8` with the range
of the maximal invalid subsequence (Unicode's recommended practice, as computed
by `String.get_utf_8_uchar`); Narya's lexer reports it as a parse error at that
range.  So positions are always exact byte positions, and the text of tokens is
always a substring of the input.

## Token layer (`Token_parser`)

A parser either succeeds with a value or fails.  "Consumed" means the token
index advanced; consuming the end of input counts.

- `return`, `succeed`, `>>=`/`let*`, `map`: as usual.
- `p </> q`: run `p`; if it fails without consuming, undo its changes to the
  user state and run `q`.  A failure after consuming propagates.
- `backtrack p _`: run `p`; if it fails, restore the index and user state and
  fail without having consumed.
- `followed_by p _`: run `p`, then restore the index and user state in either
  case; return its value or fail without having consumed.
- `optional`, `zero_or_more`, `zero_or_more_fold_left`, `one_or_more`,
  `one_or_more_fold_left`, `skip_zero_or_more`, `skip_one_or_more`: the usual
  repetitions, each iteration being an alternative in the sense of `</>` (so an
  iteration that fails without consuming ends the repetition, and one that fails
  after consuming fails it).  `parenthesized` sequences three parsers.
- `get`, `set`, `update`: the user state.
- `step _ f`: if the next item is a token `(range, tok)` and `f user range tok`
  is `Some (a, user')`, consume it, set the user state, and return `a`;
  otherwise fail without consuming.
- `expect_end a`: consume the end of input, or fail without consuming.
- `located p`: the range from the start of the first token consumed by `p` to
  the end of the last; if `p` consumes none, the zero-width range at the end of
  the last token consumed before it (or `Position.start` if there is none in
  this run).
- `fail e`: fail with semantic error `e`; `unexpected _`: fail with a syntax
  error.  A failed parse is semantic if the most recent failure was raised by
  `fail`, and syntactic otherwise (including when `backtrack` or `followed_by`
  turn a failure into their own).
- `run tokens user p`: run `p` with a fresh state, starting at the stream's
  current index and leaving it where `p` stopped on success.  The result is
  `Success`, `Failed_syntax range` (the range of the first token not consumed,
  or zero-width at the end of input), or `Failed_semantic e`.

Only `Fail.Fail` is ever caught by the combinators, never other exceptions such
as Asai's fatal errors (which the lexer raises).

## Token stream and lexer driver

- The stream is `Bof, t1, ..., tn`, then the end.  `Bof` carries the leading
  whitespace and comments; every other token carries the whitespace *after* it
  (the reformatter depends on this).  The lexer's `Eof` token is not added: when
  the lexer consumes the end of input, the stream ends.
- Tokens are lexed when a parser first looks at them, so lexer errors and
  warnings happen at the same point relative to command execution as they would
  in a push parser fed character by character.
- A lexing failure (an unterminated comment, string, hole or guillemet) is not a
  token-layer failure that `</>` could catch: when a parser asks for that
  token, the whole parse fails, with a zero-width range at the lexer's position.
  A character that cannot start any token, and invalid UTF-8, are reported by
  Narya's lexer as errors with the range of the offending bytes.
- Each command parse (`Command.Parse.parse_next`) is a fresh `run` on the same
  stream; tokens before its start are forgotten.

## Differences from fmlib-parse

Narya's output on valid input is byte-identical to what it was with fmlib
(checked on the test suite, on reformatting the first 120 symmetry-narya
modules, and on the token streams of 1000+ files).  The intentional
differences, on which nothing in Narya depended, are:

- In fmlib, `p </> q` also undid `p`'s changes to the state when `p`
  *succeeded* without consuming; and its `located` had a quirk where an inner
  `located` consuming nothing could overwrite the start of an enclosing range.
  Neither was ever triggered by Narya (checked by instrumenting both behaviours).
- fmlib's UTF-8 decoder accepted overlong encodings, turned a truncated sequence
  at the end of input into its partial value, swallowed the byte that
  interrupted a sequence, and advanced positions by the declared length of the
  sequence plus one (which could make Asai crash with "beyond eof"); its encoder
  wrote U+0080–U+008E as single raw bytes.  Invalid UTF-8 is now rejected, and
  encoding is standard.
- A character that cannot start a token was reported at a zero-width range,
  which Narya turned into an anomaly; it is now an ordinary parse error.
- fmlib tracked display columns (tabs as 4, control characters as 0); Narya
  never used them, and `Position` no longer has them.
- Expectation messages, indentation-sensitive parsing, and incremental feeding
  are not provided.
