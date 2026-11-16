open Fparse
open Token
open Core
open Reporter

module Token_whitespace = struct
  type t = Token.t * Whitespace.t list
end

module Located_token = struct
  type t = Position.range * Token_whitespace.t
end

(* The lexer is written in direct style, as functions on the state of a basic utf-8 character parser: "peek" looks at the next character (as a scalar, or -1 at the end of input), "junk" consumes the character just peeked at, and "fail" fails.  A failure after consuming characters is a lexing error; a failure without consuming means that this kind of token doesn't start here. *)
module Basic = Ucharacter

let fail = Basic.syntax_fail
let peek = Basic.peek
let junk = Basic.junk
let text = Basic.text
let index = Basic.index
let position = Basic.current_position
let add_scalar = Utf8.Encoder.add_scalar

(* Run a lexer that may fail without consuming, restoring the state if it fails. *)
let attempt (p : Basic.state -> 'a) (st : Basic.state) : 'a option =
  match Basic.backtrack p st with
  | x -> Some x
  | exception Fparse.Fail.Fail -> None

let backquote = 0x60
let newline = 0x0A
let lbrace = 0x7B
let rbrace = 0x7D
let dquote = 0x22
let caret = 0x5E
let hash = 0x23
let dot = 0x2E
let lparen = 0x28
let rparen = 0x29
let is_digit_scalar v = v >= 0x30 && v <= 0x39

(* Consume characters while they satisfy f (which is never asked about the end of input). *)
let rec skip_while (f : int -> bool) (st : Basic.state) : unit =
  let v = peek st in
  if v >= 0 && f v then (
    junk st v;
    skip_while f st)

(* A line comment starts with a backquote and extends to the end of the line.  This is called after the backquote. *)
let line_comment_rest st : string =
  let start = index st in
  skip_while (fun v -> v <> newline) st;
  text st start (index st)

(* A block comment starts with {` and ends with `}, and can be nested.  This consumes the {` if it is there. *)
let block_comment_start st : bool =
  Option.is_some
    (attempt
       (fun st ->
         let v = peek st in
         if v <> lbrace then fail st
         else (
           junk st v;
           let v = peek st in
           if v <> backquote then fail st else junk st v))
       st)

(* The rest of a block comment, after the {`. *)
let block_comment_rest st : string =
  let state_of c = if c = lbrace then `LBrace else if c = backquote then `Backquote else `None in
  let buf = Buffer.create 32 in
  let rec rest nesting prev =
    let c = peek st in
    if c < 0 then fail st
    else (
      junk st c;
      match prev with
      | `LBrace when c = backquote ->
          Buffer.add_char buf '`';
          rest (nesting + 1) `None
      | `Backquote when c = rbrace ->
          if nesting <= 0 then Buffer.contents buf
          else (
            Buffer.add_string buf "`}";
            rest (nesting - 1) `None)
      | `Backquote when c = backquote ->
          Buffer.add_char buf '`';
          rest nesting `Backquote
      | `Backquote ->
          Buffer.add_char buf '`';
          add_scalar buf c;
          rest nesting (state_of c)
      | _ when c = backquote -> rest nesting `Backquote
      | _ ->
          add_scalar buf c;
          rest nesting (state_of c)) in
  rest 0 `None

let is_space v = v = 0x20 || v = 0x09 || v = newline || v = 0x0D

(* Whitespace consists of spaces, tabs, newlines, and comments.  We record the comments, and the number of newlines in each run of spaces, tabs, and newlines when it is positive.  If such a run follows a line comment, we don't count the newline that *ended* the line comment. *)
let whitespace st : Whitespace.t list =
  let rec loop acc after_line_comment =
    let v = peek st in
    if v = backquote then (
      junk st v;
      let c = line_comment_rest st in
      loop (`Line c :: acc) true)
    else if v = lbrace && block_comment_start st then
      let c = block_comment_rest st in
      loop (`Block c :: acc) false
    else if v >= 0 && is_space v then
      let rec count n =
        let v = peek st in
        if v >= 0 && is_space v then (
          junk st v;
          count (if v = newline then n + 1 else n))
        else n in
      let n = count 0 in
      let n = if after_line_comment then n - 1 else n in
      loop (if n = 0 then acc else `Newlines n :: acc) false
    else List.rev acc in
  loop [] false

(* A quoted string starts and ends with double-quotes, and allows backslash-quoted double-quotes and backslashes inside.  This is called at the opening double-quote. *)
let quoted_string st : Token.t =
  junk st dquote;
  let buf = Buffer.create 16 in
  let rec rest state =
    let c = peek st in
    if c < 0 then fail st
    else (
      junk st c;
      match (state, c) with
      | (`None | `Backquote), 0x22 -> String (Buffer.contents buf)
      | (`None | `Backquote), 0x5C -> rest `Quoted
      | _, 0x60 ->
          Buffer.add_char buf '`';
          rest `Backquote
      | `Backquote, 0x7D ->
          emit Comment_end_in_string;
          Buffer.add_char buf '}';
          rest `None
      | _, c ->
          add_scalar buf c;
          rest `None) in
  rest `None

let query = 0x3F
let invquery = 0xBF (* ¿ *)
let dblquery = 0x2047 (* ⁇ *)
let gelded_query = 0x0294 (* ʔ *)
let is_digit c = String.exists (fun x -> x = c) "0123456789"

(* A hole is either the single character ?, or a hole with contents that start with ¿ and ends with ʔ.  Even comment sequences inside of a hole are ignored.  Holes with contents can be nested.  This is called at the ¿, and returns the contents including the delimiters. *)
let hole_contents st : string =
  let start = index st in
  junk st invquery;
  let rec go depth =
    let v = peek st in
    if v < 0 then fail st
    else (
      junk st v;
      if v = gelded_query then if depth = 0 then () else go (depth - 1)
      else if v = invquery then go (depth + 1)
      else go depth) in
  go 0;
  text st start (index st)

(* A numbered hole, after the ⁇. *)
let numbered_hole st : Token.t =
  let start = index st in
  skip_while is_digit_scalar st;
  if index st = start then fail st
  else
    let number = text st start (index st) in
    let v = peek st in
    if v = query then (
      junk st v;
      Hole { number = Some number; contents = None })
    else if v = invquery then
      let contents = hole_contents st in
      Hole { number = Some number; contents = Some contents }
    else fail st

let hole st v : Token.t =
  if v = query then (
    junk st v;
    Hole { number = None; contents = None })
  else if v = invquery then
    let contents = hole_contents st in
    Hole { number = None; contents = Some contents }
  else if v = dblquery then (
    junk st v;
    match attempt numbered_hole st with
    | Some tok -> tok
    | None -> DblQuery)
  else (
    (* Grab other hole-like sequences, which won't parse but which we don't want the user to use elsewhere. *)
    junk st v;
    GeldedQuery)

module Specials = struct
  (* Any of these characters is always its own token. *)
  let default_onechar_ops =
    [|
      (0x28, LParen);
      (* ( *)
      (0x29, RParen);
      (* ) *)
      (0x5B, LBracket);
      (* [ *)
      (0x5D, RBracket);
      (* ] *)
      (0x7B, LBrace);
      (* { *)
      (0x7D, RBrace);
      (* } *)
      (0x21A6, Mapsto);
      (* ↦ *)
      (0x2907, DblMapsto);
      (* ⤇ *)
      (0x2192, Arrow);
      (* → *)
      (0x21D2, DblArrow);
      (* ⇒ *)
      (0x2254, Coloneq);
      (* ≔ *)
      (0x2A74, DblColoneq);
      (* ⩴ *)
      (0x2A72, Pluseq);
      (* ⩲ *)
      (0x2026, Ellipsis);
      (* … *)
    |]

  (* Any sequence consisting entirely of these characters is its own token. *)
  let default_ascii_symbols =
    [|
      '~'; '!'; '@'; '#'; '$'; '%'; '&'; '*'; '/'; '='; '+'; '|'; ','; '<'; '>'; ':'; ';'; '-'; '^';
    |]

  module Data = struct
    type t = {
      onechar_ops : (int * Token.t) Array.t;
      ascii_symbols : char Array.t;
      digit_vars : bool;
    }
  end

  (* The current data is read several times for every character lexed, so we store it in a plain reference rather than using a Reader effect.  Performing an effect costs time proportional to the number of handlers installed between the "perform" and its handler, and since "run" is called outside everything else, that includes all the handlers installed by every enclosing "import" of a file being loaded from source. *)
  let current : Data.t option ref = ref None

  let run ?(onechar_ops = Array.of_list []) ?(ascii_symbols = Array.of_list []) ?(digit_vars = true)
      f =
    (* Caller-supplied one-char ops come first so they override any default with the same character
       (e.g. a caller reclaiming ⇒ as a plain identifier rather than the built-in DblArrow). *)
    let onechar_ops = Array.append onechar_ops default_onechar_ops in
    let ascii_symbols = Array.append default_ascii_symbols ascii_symbols in
    let old = !current in
    current := Some { onechar_ops; ascii_symbols; digit_vars };
    Fun.protect ~finally:(fun () -> current := old) f

  let read () =
    match !current with
    | Some data -> data
    | None -> failwith "Lexer.Specials.run not called"

  let onechar_ops () = (read ()).onechar_ops
  let ascii_symbols () = (read ()).ascii_symbols
  let digit_vars () = (read ()).digit_vars
end

(* The following arrays are computed from the current special-character data, and are consulted for every character lexed.  So we remember the last one computed, along with the data it was computed from, and recompute it only when that data changes. *)
let memo : (Specials.Data.t -> 'a) -> unit -> 'a =
 fun f ->
  let cache = ref None in
  fun () ->
    let data = Specials.read () in
    match !cache with
    | Some (data', value) when data' == data -> value
    | _ ->
        let value = f data in
        cache := Some (data, value);
        value

let onechar_uchars = memo (fun data -> Array.map (fun c -> Uchar.of_int (fst c)) data.onechar_ops)
let onechar_tokens = memo (fun data -> Array.map snd data.onechar_ops)
let onechar_codes = memo (fun data -> Array.map fst data.onechar_ops)

(* The index of a one-character operator, or -1. *)
let find_onechar v =
  let codes = onechar_codes () in
  let rec go i = if i >= Array.length codes then -1 else if codes.(i) = v then i else go (i + 1) in
  go 0

let ascii_symbol_uchars = memo (fun data -> Array.map Uchar.of_char data.ascii_symbols)

let ascii_symbol_table =
  memo (fun data -> Array.init 128 (fun c -> Array.mem (Char.chr c) data.ascii_symbols))

let is_ascii_symbol_scalar v = v >= 0 && v < 128 && (ascii_symbol_table ()).(v)

let ascii_op st : Token.t =
  let start = index st in
  skip_while is_ascii_symbol_scalar st;
  match text st start (index st) with
  | "->" -> Arrow
  | "=>" -> DblArrow
  | "|->" -> Mapsto
  | "|=>" -> DblMapsto
  | ":=" -> Coloneq
  | "::=" -> DblColoneq
  | "+=" -> Pluseq
  | ":" -> Colon
  | "..." -> Ellipsis
  | op -> Op op

let super_lparen = Uchar.to_int Token.super_lparen_uchar
let super_rparen = Uchar.to_int Token.super_rparen_uchar
let is_super v = v >= 0 && Array.mem (Uchar.unsafe_of_int v) Token.super_uchars

(* A Unicode superscript is a string of Unicode superscript numbers and letters between superscript parentheses.  We don't ever want to fail lexing, so any string starting with a superscript left parenthesis that *doesn't* look like this, or a superscript right parenthesis occurring before a superscript left parenthesis, is lexed as an "invalid superscript".  This is called at a superscript parenthesis. *)
let utf8_superscript st v : Token.t =
  junk st v;
  if v = super_rparen then Invalid_superscript ")"
  else
    let w = peek st in
    if is_super w then (
      let start = index st in
      skip_while is_super st;
      let s = Token.of_super (text st start (index st)) in
      let w = peek st in
      if w = super_rparen then (
        junk st w;
        Superscript s)
      else Invalid_superscript ("(" ^ s))
    else if w = super_rparen then (
      junk st w;
      Invalid_superscript "()")
    else Invalid_superscript "("

let is_unsuper v = v >= 0 && v < 128 && Array.mem (Char.chr v) Token.unsupers

(* An ASCII superscript is a double caret followed (without any space) by a string of numbers and letters between parentheses.  We don't ever want to fail lexing, so any string starting with a double caret that doesn't look like this is lexed as an "invalid superscript".  (Single carats can be ASCII operators, so this fails without consuming if there is only one.) *)
let caret_superscript st : Token.t =
  junk st caret;
  let v = peek st in
  if v <> caret then fail st
  else (
    junk st v;
    let v = peek st in
    if v = lparen then (
      junk st v;
      let w = peek st in
      if is_unsuper w then (
        let start = index st in
        skip_while is_unsuper st;
        let s = text st start (index st) in
        let w = peek st in
        if w = rparen then (
          junk st w;
          Superscript s)
        else Invalid_superscript ("(" ^ s))
      else if w = rparen then (
        junk st w;
        Invalid_superscript "()")
      else Invalid_superscript "(")
    else Invalid_superscript "")

(* For other identifiers, we consume (utf-8) characters until we reach whitespace or a special symbol.  Here's the set of specials., as a hashtable since we test every character of every identifier for membership in it. *)
module Uchars = Hashtbl.Make (Uchar)

let specials =
  memo @@ fun _ ->
  let specials = Uchars.create 300 in
  Array.iter (fun c -> Uchars.replace specials c ())
  @@ Array.concat
       [
         ascii_symbol_uchars ();
         onechar_uchars ();
         (* We also have to stop when we meet a line comment started by a backquote.  We don't have to worry about block comments, since their opening brace is a onechar op and hence also stops an identifier. *)
         Array.map Uchar.of_char [| ' '; '\t'; '\n'; '\r'; '`' |];
         (* We only include the superscript parentheses: other superscript characters without parentheses are allowed in identifiers. *)
         [| Token.super_lparen_uchar; Token.super_rparen_uchar |];
         (* Hole symbols also stop us *)
         Array.map Uchar.of_int [| query; dblquery; invquery; gelded_query |];
         (* Unicode tag characters are special *)
         Array.init (16 * 6) (fun i -> Uchar.of_int (0xE0020 + i));
         (* Finally, we exclude dots, because they are treated specially as separating pieces of an identifier *)
         [| Uchar.of_char '.' |];
       ];
  specials

(* Whether a character can occur in an identifier.  ASCII characters are looked up in a table. *)
let ascii_specials =
  memo (fun _ -> Array.init 128 (fun c -> Uchars.mem (specials ()) (Uchar.of_int c)))

let is_other_char v =
  if v < 128 then v >= 0 && not (ascii_specials ()).(v)
  else not (Uchars.mem (specials ()) (Uchar.unsafe_of_int v))

let all_digits = String.for_all is_digit
let is_numeral = List.for_all all_digits

(* Whether a string is valid as a dot-separated piece of an identifier name, or equivalently as a local variable name.  We don't test for absence of the delimited symbols, since they will automatically be lexed separately; this is for testing validity after the lexer has split things into potential tokens.  We also don't test for absence of dots, since identifiers will be split on dots automatically. *)
let atomic_ident s =
  String.length s > 0
  && s.[0] <> '_'
  && (Specials.digit_vars () || not (is_digit s.[0]))
  && not (all_digits s)

let valid_var = atomic_ident

(* A field name is like an identifier, but it could be all numeric for positional projections. *)
let valid_field s =
  String.length s > 0
  && s.[0] <> '_'
  && (Specials.digit_vars () || (not (is_digit s.[0])) || all_digits s)

let valid_ident = List.for_all atomic_ident

(* Identifiers quoted by guillemets *)
let guillemet_start = 0xAB
let guillemet_end = 0xBB

(* A sequence of identifier characters (notably not including dots), or a word quoted by guillemets (which can be nested).  Not necessarily valid as an identifier.  This is called at its first character, v. *)
let other_word st v : string =
  let start = index st in
  junk st v;
  if v = guillemet_start then
    let rec go n =
      let c = peek st in
      if c < 0 then fail st
      else (
        junk st c;
        if c = guillemet_end then if n = 1 then () else go (n - 1)
        else if c = guillemet_start then go (n + 1)
        else go n) in
    go 1
  else skip_while is_other_char st;
  text st start (index st)

let at_word_start v = v = guillemet_start || is_other_char v

(* One or more dots, at the first one. *)
let dots st : int =
  let rec go n =
    let v = peek st in
    if v = dot then (
      junk st v;
      go (n + 1))
    else n in
  go 0

(* A dot-separated token is a sequence of other_words separated by some number of dots, without any spaces or special characters. *)
let rec after_dots st acc =
  let v = peek st in
  if at_word_start v then
    let atom = other_word st v in
    after_atom st (`Atom atom :: acc)
  else List.rev acc

and after_atom st acc =
  if peek st = dot then
    let n = dots st in
    after_dots st (`Dots n :: acc)
  else List.rev acc

let atomic_other_token st : [ `Dots of int | `Atom of string ] list =
  let v = peek st in
  if at_word_start v then
    let atom = other_word st v in
    after_atom st [ `Atom atom ]
  else fail st

let dot_separated_token st : [ `Dots of int | `Atom of string ] list =
  if peek st = dot then
    let n = dots st in
    after_dots st [ `Dots n ]
  else atomic_other_token st

(* Check for notation parts that are reserved words or single underscores. *)
let get_reserved_word = function
  | "let" -> Some Let
  | "rec" -> Some Rec
  | "only" -> Some Only
  | "lock" -> Some Lock
  | "key" -> Some Keyword_key
  | "in" -> Some In
  | "axiom" -> Some Axiom
  | "def" -> Some Def
  | "and" -> Some And
  | "echo" -> Some Echo
  | "synth" -> Some Synth
  | "about" -> Some About
  | "quit" -> Some Quit
  | "match" -> Some Match
  | "return" -> Some Return
  | "sig" -> Some Sig
  | "data" -> Some Data
  | "codata" -> Some Codata
  | "notation" -> Some Notation
  | "import" -> Some Import
  | "export" -> Some Export
  | "chdir" -> Some Chdir
  | "solve" -> Some Solve
  | "split" -> Some Split
  | "show" -> Some Show
  | "display" -> Some Display
  | "option" -> Some Option
  | "undo" -> Some Undo
  | "section" -> Some Section
  | "fmt" -> Some Fmt
  | "end" -> Some End
  | "_" -> Some Underscore
  | _ -> None

let is_single_reserved_word = function
  | [ `Atom str ] -> get_reserved_word str
  | _ -> None

let rec contains_reserved_word = function
  | [] -> false
  | `Dots _ :: parts -> contains_reserved_word parts
  | `Atom str :: parts -> Option.is_some (get_reserved_word str) || contains_reserved_word parts

(* An identifier contains strings separated by single dots in the middle.  They can be digit strings because this could be a numeral, and they could also be the suffix of a cube variable. *)
let rec get_ident = function
  | [ `Atom str ] -> Some [ str ]
  | `Atom str :: `Dots 1 :: rest -> (
      match get_ident rest with
      | Some id -> Some (str :: id)
      | None -> None)
  | _ -> None

let rec get_higher_parts = function
  | [ `Atom str ] -> Some ([ str ], false)
  | [ `Atom str; `Dots 1 ] -> Some ([ str ], true)
  | `Atom str :: `Dots 1 :: rest -> (
      match get_higher_parts rest with
      | Some (parts, enddot) -> Some (str :: parts, enddot)
      | None -> None)
  | _ -> None

let canonicalize (loc : Asai.Range.t) (parts : [ `Dots of int | `Atom of string ] list) : Token.t =
  match is_single_reserved_word parts with
  | Some tok -> tok
  | None -> (
      if contains_reserved_word parts then fatal ~loc (Parse_error "reserved word in identifier")
      else
        match parts with
        | [ `Dots 1 ] -> Dot
        | [ `Dots 3 ] -> Ellipsis
        (* Simple field (allowed to be positional) *)
        | [ `Dots 1; `Atom fld ] when valid_field fld -> Field (fld, [])
        (* Higher field with one suffix (not allowed to be positional) *)
        | [ `Dots 1; `Atom fld; `Dots 1; `Atom pbij ] when atomic_ident fld ->
            Field (fld, String.fold_right (fun c s -> String.make 1 c :: s) pbij [])
        (* Higher field with multiple suffixes (not allowed to be positional) *)
        | `Dots 1 :: `Atom fld :: `Dots 2 :: rest when atomic_ident fld -> (
            match get_higher_parts rest with
            | Some (parts, false) -> Field (fld, parts)
            | _ -> fatal ~loc (Parse_error "invalid higher field 1"))
        (* Simple constructor *)
        | [ `Atom con; `Dots 1 ] when atomic_ident con -> Constr (con, [])
        (* Higher constructor with multiple suffixes *)
        | `Atom con :: `Dots 2 :: rest when atomic_ident con ->
            let _ =
              match get_higher_parts rest with
              | Some (parts, true) -> Constr (con, parts)
              | _ -> fatal ~loc (Parse_error "invalid higher field 2") in
            fatal ~loc (Unimplemented "higher constructors")
        (* Higher constructor with single suffix *)
        | [ `Atom con; `Dots 1; `Atom pbij; `Dots 1 ] when atomic_ident con ->
            let _ = Constr (con, String.fold_right (fun c s -> String.make 1 c :: s) pbij []) in
            fatal ~loc (Unimplemented "higher constructors")
        (* Identifier *)
        | _ -> (
            match get_ident parts with
            | Some id -> Ident id
            | None -> fatal ~loc (Parse_error "invalid identifier")))

let other st : Token.t =
  let p1 = position st in
  let parts = dot_separated_token st in
  canonicalize (Range.convert (p1, position st)) parts

(* A Key is the character # followed immediately (no intervening space) by a dot-separated identifier.  If # is not immediately followed by an identifier, this fails without consuming, so that # is instead lexed as an ordinary ASCII symbol (Op "#"), which is used e.g. for attributes. *)
let key st : Token.t =
  junk st hash;
  let parts = atomic_other_token st in
  match get_ident parts with
  | Some id -> Key id
  | None -> fail st

(* A token is a hole, a quoted string, a single-character operator, a superscript, a key, an operator of special ASCII symbols, or something else, tried in that order.  This is called at its first character, v. *)
let token_body st v : Token.t =
  if v = query || v = invquery || v = dblquery || v = gelded_query then hole st v
  else if v = dquote then quoted_string st
  else
    let i = find_onechar v in
    if i >= 0 then (
      junk st v;
      (onechar_tokens ()).(i))
    else if v = super_lparen || v = super_rparen then utf8_superscript st v
    else
      match if v = caret then attempt caret_superscript st else None with
      | Some tok -> tok
      | None -> (
          match if v = hash then attempt key st else None with
          | Some tok -> tok
          | None ->
              if is_ascii_symbol_scalar v then ascii_op st
              else if v = dot || at_word_start v then other st
              else
                (* No token can start with this character (e.g. a Unicode tag character). *)
                fatal
                  ~loc:(Range.convert (Basic.peeked_range st))
                  (Parse_error (Printf.sprintf "invalid character U+%04X" v)))

(* We include whitespace *after* the token, so that we can save comments occurring after any code.  At the end of input, we produce Eof (and consume the end). *)
let token st : Located_token.t =
  let v = peek st in
  let p1 = position st in
  if v < 0 then Basic.expect_end ((p1, p1), (Eof, [])) st
  else
    let tok = token_body st v in
    let p2 = position st in
    let ws = whitespace st in
    ((p1, p2), (tok, ws))

(* This means we need a separate combinator to parse any initial whitespace.   *)
let bof st : Located_token.t =
  let ws = whitespace st in
  let p = position st in
  ((p, p), (Bof, ws))

(* The token stream of a source string, lexed on demand as parsers ask for tokens.  The first token is Bof, holding any initial whitespace; each later token is lexed by "token", starting with a fresh lexer state at the point where the previous one stopped.  The Eof token is not added to the stream: when the lexer consumes the end of input, the stream ends instead. *)
let tokens (src : string) : Token_whitespace.t Tokens.t =
  let st = Basic.init src in
  let started = ref false in
  Tokens.make @@ fun () ->
  let p =
    if !started then token
    else (
      started := true;
      bof) in
  match Basic.run st p with
  | Some tok -> if Basic.has_consumed_end st then End (Basic.current_position st) else Token tok
  | None -> Failed (Basic.current_position st)
  | exception Basic.Invalid_utf8 rng -> fatal ~loc:(Range.convert rng) (Parse_error "invalid UTF-8")

module Single_token = struct
  module Basic = Token_parser.Make (Unit) (Token_whitespace) (Token_whitespace) (Unit)
  open Basic

  let token : Token_whitespace.t t = step "token" (fun state _ tok -> Some (tok, state))

  (* Bof, then one token, then the end. *)
  let start : Token_whitespace.t t =
    let* _ = token in
    let* tok = token in
    expect_end tok
end

let single str =
  (* The lexer performs Range effects, so we have to set up handlers for those. *)
  let env : Range.Data.t =
    { source = `String { content = str; title = None }; length = Int64.of_int (String.length str) }
  in
  Range.run ~env @@ fun () ->
  match Single_token.Basic.run (tokens str) () Single_token.start with
  | Success (tok, ws) -> if ws = [] then Some tok else None
  | Failed_syntax _ | Failed_semantic _ -> None
