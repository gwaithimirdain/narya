open Bwd
open Fmlib_parse
open Token
open Core
open Reporter

(* NB: The parsing combinator "string" just parses the characters in the string one by one.  This means that if it succeeds to parse the first character in the string, it consumes that character, and if it fails later in the string then parsing dies completely.  If that's not what you want, which it usually isn't, you need to wrap it in "backtrack".  *)

module Token_whitespace = struct
  type t = Token.t * Whitespace.t list
end

module Located_token = struct
  type t = Position.range * Token_whitespace.t
end

(* As the lexer "state" we remember whether we just saw a line comment. *)
module LexerState = struct
  type t = [ `Linecomment | `None ]
end

(* We define the lexer using a basic utf-8 character parser from Fmlib. *)
module Basic = Ucharacter.Make_utf8 (LexerState) (Located_token) (Unit)
open Basic

let backquote = Uchar.of_char '`'
let newline = Uchar.of_char '\n'
let lbrace = Uchar.of_char '{'
let rbrace = Uchar.of_char '}'

(* A line comment starts with a backquote and extends to the end of the line.  *)
let line_comment : Whitespace.t t =
  let* c = uword (fun c -> c = backquote) (fun c -> c <> newline) "line comment" in
  let* () = set `Linecomment in
  return (`Line (String.sub c 1 (String.length c - 1)))

(* A block comment starts with {` and ends with `}, and can be nested.  *)
let block_comment : Whitespace.t t =
  let state_of c = if c = lbrace then `LBrace else if c = backquote then `Backquote else `None in
  let rec rest buf nesting prev =
    let* c = ucharp (fun _ -> true) "any character" in
    match prev with
    | `LBrace when c = backquote -> rest (buf ^ "`") (nesting + 1) `None
    | `Backquote when c = rbrace ->
        if nesting <= 0 then return (`Block buf) else rest (buf ^ "`}") (nesting - 1) `None
    | `Backquote when c = backquote -> rest (buf ^ "`") nesting `Backquote
    | `Backquote -> rest (buf ^ "`" ^ Utf8.Encoder.to_internal c) nesting (state_of c)
    | _ when c = backquote -> rest buf nesting `Backquote
    | _ -> rest (buf ^ Utf8.Encoder.to_internal c) nesting (state_of c) in
  let* _ = backtrack (string "{`") "\"{`\"" in
  let* () = set `None in
  rest "" 0 `None

(* This combinator parses not just newlines but also spaces and tabs, but it only counts the number of newlines.  Thus it returns (`Newlines 0) if it parses only spaces and tabs (possibly including the newline at the end of a preceding line comment). *)
let newlines : Whitespace.t t =
  let* n =
    one_or_more_fold_left
      (fun c -> return (if c = '\n' then 1 else 0))
      (fun n c -> return (if c = '\n' then n + 1 else n))
      (one_of_chars " \t\n\r" "space, tab, or newline") in
  let* line = get in
  let* () = set `None in
  (* If we just saw a line comment, then we don't include the newline that *ended* the line comment as a "newline". *)
  return (`Newlines (if line = `Linecomment then n - 1 else n))

(* Whitespace.t consists of spaces, tabs, newlines, and comments.  We only record newlines when there are a positive number of them. *)
let whitespace : Whitespace.t list t =
  let* () = set `None in
  let* ws =
    zero_or_more_fold_left Emp
      (fun ws w -> if w = `Newlines 0 then return ws else return (Snoc (ws, w)))
      (line_comment </> block_comment </> newlines)
    |> no_expectations in
  return (Bwd.to_list ws)

(* A quoted string starts and ends with double-quotes, and allows backslash-quoted double-quotes and backslashes inside. *)
let quoted_string : Token.t t =
  let* _ = char '"' in
  let rec rest state str =
    let* c = ucharp (fun _ -> true) "any character" in
    match (state, Utf8.Encoder.to_internal c) with
    | `None, "\"" | `Backquote, "\"" -> return (String str)
    | `None, "\\" | `Backquote, "\\" -> rest `Quoted str
    | _, "`" -> rest `Backquote (str ^ "`")
    | `Backquote, "}" ->
        emit Comment_end_in_string;
        rest `None (str ^ "}")
    | _, c -> rest `None (str ^ c) in
  rest `None ""

let query = Uchar.of_char '?'
let bang = Uchar.of_char '!'
let query_bang = Uchar.of_int 0x2048 (* ⁈ *)
let bang_query = Uchar.of_int 0x2049 (* ⁉ *)
let query_query = Uchar.of_int 0x2047 (* ⁇ *)
let bang_bang = Uchar.of_int 0x203C (* ‼ *)
let is_digit c = String.exists (fun x -> x = c) "0123456789"

(* A hole is either the single character ?, or a hole with contents that start with ?! or ⁈ and ends with !? or ⁉, with internal parts separated by !.  Even comment sequences inside of a hole are ignored. *)
let rec hole_contents () : string list t =
  let* first =
    zero_or_more_fold_left ""
      (fun s c -> return (s ^ Utf8.Encoder.to_internal c))
      (ucharp (fun c -> c <> bang && c <> bang_query) "hole contents") in
  (let* _ = uchar bang in
   (let* _ = uchar query in
    return [ first ])
   </> let* rest = hole_contents () in
       return (first :: rest))
  </>
  let* _ = uchar bang_query in
  return [ first ]

let hole : Token.t t =
  (let* _ = uchar query in
   (let* _ = uchar bang in
    let* contents = hole_contents () in
    return (Hole (Some contents)))
   </> (let* _ = uchar query in
        (* Numbered hole *)
        (let* _ = word is_digit is_digit "hole number" in
         (let* _ = uchar query in
          (let* _ = uchar bang in
           let* contents = hole_contents () in
           return (Hole (Some contents)))
          </> return (Hole None))
         </> let* _ = uchar query_bang in
             let* contents = hole_contents () in
             return (Hole (Some contents)))
        </> return DblQuery)
   </> return (Hole None))
  </> (let* _ = uchar query_bang in
       let* contents = hole_contents () in
       return (Hole (Some contents)))
  </> (let* _ = uchar query_query in
       (let* _ = word is_digit is_digit "hole number" in
        (let* _ = uchar query in
         (let* _ = uchar bang in
          let* contents = hole_contents () in
          return (Hole (Some contents)))
         </> return (Hole None))
        </> let* _ = uchar query_bang in
            let* contents = hole_contents () in
            return (Hole (Some contents)))
       </> return DblQuery)
  (* Grab other hole-like sequences, which won't parse but which we don't want the user to use elsewhere. *)
  </> (let* _ = uchar bang in
       (let* _ = uchar bang in
        return DblBang)
       </> (let* _ = uchar query in
            return BangQuery)
       </> return Bang)
  </> (let* _ = uchar bang_query in
       return BangQuery)
  </> let* _ = uchar bang_bang in
      return DblBang

module Specials = struct
  (* Any of these characters is always its own token. *)
  let default_onechar_ops =
    [|
      (0x28, LParen);
      (0x29, RParen);
      (0x5B, LBracket);
      (0x5D, RBracket);
      (0x7B, LBrace);
      (0x7D, RBrace);
      (0x21A6, Mapsto);
      (0x2907, DblMapsto);
      (0x2192, Arrow);
      (0x21D2, DblArrow);
      (0x2254, Coloneq);
      (0x2A74, DblColoneq);
      (0x2A72, Pluseq);
      (0x2026, Ellipsis);
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

  module R = Algaeff.Reader.Make (Data)

  let () = R.register_printer (function `Read -> Some "unhandled Lexer.Specials read effect")

  let run ?(onechar_ops = Array.of_list []) ?(ascii_symbols = Array.of_list []) ?(digit_vars = true)
      f =
    let onechar_ops = Array.append default_onechar_ops onechar_ops in
    let ascii_symbols = Array.append default_ascii_symbols ascii_symbols in
    R.run ~env:{ onechar_ops; ascii_symbols; digit_vars } f

  let onechar_ops () = (R.read ()).onechar_ops
  let ascii_symbols () = (R.read ()).ascii_symbols
  let digit_vars () = (R.read ()).digit_vars
end

let onechar_uchars () = Array.map (fun c -> Uchar.of_int (fst c)) (Specials.onechar_ops ())
let onechar_tokens () = Array.map snd (Specials.onechar_ops ())

let onechar_op : Token.t t =
  let* c = ucharp (fun c -> Array.mem c (onechar_uchars ())) "one-character operator" in
  let i = Option.get (Array.find_index (fun x -> x = c) (onechar_uchars ())) in
  return (onechar_tokens ()).(i)

let ascii_symbol_uchars () = Array.map Uchar.of_char (Specials.ascii_symbols ())
let is_ascii_symbol c = Array.mem c (Specials.ascii_symbols ())

let ascii_op : Token.t t =
  let* op = word is_ascii_symbol is_ascii_symbol "ASCII symbol" in
  match op with
  | "->" -> return Arrow
  | "=>" -> return DblArrow
  | "|->" -> return Mapsto
  | "|=>" -> return DblMapsto
  | ":=" -> return Coloneq
  | "::=" -> return DblColoneq
  | "+=" -> return Pluseq
  | ":" -> return Colon
  | "..." -> return Ellipsis
  | _ -> return (Op op)

(* A Unicode superscript is a string of Unicode superscript numbers and letters between superscript parentheses.  We don't ever want to fail lexing, so any string starting with a superscript left parenthesis that *doesn't* look like this, or a superscript right parenthesis occurring before a superscript left parenthesis, is lexed as an "invalid superscript". *)
let utf8_superscript =
  (let* _ = uchar Token.super_lparen_uchar in
   (let* s =
      uword
        (fun c -> Array.mem c Token.super_uchars)
        (fun c -> Array.mem c Token.super_uchars)
        "utf-8 superscript" in
    (let* _ = uchar Token.super_rparen_uchar in
     return (Superscript (Token.of_super s)))
    </> return (Invalid_superscript ("(" ^ Token.of_super s)))
   </> (let* _ = uchar Token.super_rparen_uchar in
        return (Invalid_superscript "()"))
   </> return (Invalid_superscript "("))
  </> let* _ = uchar Token.super_rparen_uchar in
      return (Invalid_superscript ")")

(* An ASCII superscript is a double caret followed (without any space) by a string of numbers and letters between parentheses.  We don't ever want to fail lexing, so any string starting with a double caret that doesn't look like this is lexed as an "invalid superscript".  (Single carats can be ASCII operators.) *)
let caret_superscript =
  backtrack
    (let* _ = string "^^" in
     (let* _ = char '(' in
      (let* s =
         word
           (fun x -> Array.mem x Token.unsupers)
           (fun x -> Array.mem x Token.unsupers)
           "caret superscript" in
       (let* _ = char ')' in
        return (Superscript s))
       </> return (Invalid_superscript ("(" ^ s)))
      </> (let* _ = char ')' in
           return (Invalid_superscript "()"))
      </> return (Invalid_superscript "("))
     </> return (Invalid_superscript ""))
    ""

let superscript = utf8_superscript </> caret_superscript

(* For other identifiers, we consume (utf-8) characters until we reach whitespace or a special symbol.  Here's the set of specials. *)
let specials () =
  Array.concat
    [
      ascii_symbol_uchars ();
      onechar_uchars ();
      (* We also have to stop when we meet a line comment started by a backquote.  We don't have to worry about block comments, since their opening brace is a onechar op and hence also stops an identifier. *)
      Array.map Uchar.of_char [| ' '; '\t'; '\n'; '\r'; '`' |];
      (* We only include the superscript parentheses: other superscript characters without parentheses are allowed in identifiers. *)
      [| Token.super_lparen_uchar; Token.super_rparen_uchar |];
      (* Hole symbols also stop us *)
      [| query; bang; query_bang; bang_query; query_query; bang_bang |];
      (* Unicode tag characters are special *)
      Array.init (16 * 6) (fun i -> Uchar.of_int (0xE0020 + i));
      (* Finally, we exclude dots, because they are treated specially as separating pieces of an identifier *)
      [| Uchar.of_char '.' |];
    ]

let other_char : string t =
  let* c = ucharp (fun x -> not (Array.mem x (specials ()))) "alphanumeric or unicode" in
  return (Utf8.Encoder.to_internal c)

let all_digits = String.for_all is_digit
let is_numeral = List.for_all all_digits
let valid_var x = not (all_digits x)

(* Whether a string is valid as a dot-separated piece of an identifier name, or equivalently as a local variable name.  We don't test for absence of the delimited symbols, since they will automatically be lexed separately; this is for testing validity after the lexer has split things into potential tokens.  We also don't test for absence of dots, since identifiers will be split on dots automatically. *)
let atomic_ident s =
  String.length s > 0
  && s.[0] <> '_'
  && (Specials.digit_vars () || s.[0] < '0' || s.[1] > '9')
  && not (all_digits s)

(* A field name is like an identifier, but it could be all numeric for positional projections. *)
let valid_field s =
  String.length s > 0
  && s.[0] <> '_'
  && ((Specials.digit_vars () || s.[0] < '0' || s.[1] > '9') || all_digits s)

let valid_ident = List.for_all atomic_ident

(* Identifiers quoted by guillemets *)
let guillemet_start = Uchar.of_int 0xAB
let guillemet_end = Uchar.of_int 0xBB

let rec guillemeted_word buf n =
  let* c = ucharp (fun _ -> true) "any" in
  let buf = buf ^ Utf8.Encoder.to_internal c in
  if c = guillemet_end then if n = 1 then return buf else guillemeted_word buf (n - 1)
  else if c = guillemet_start then guillemeted_word buf (n + 1)
  else guillemeted_word buf n

(* A sequence of other_chars, notably not including dots.  Not necessarily valid as an identifier. *)
let other_word =
  (let* _ = uchar guillemet_start in
   guillemeted_word "«" 1)
  </> one_or_more_fold_left return (fun str c -> return (str ^ c)) other_char

(* One or more dots. *)
let dots = skip_one_or_more (char '.')

(* An dot_separated_token is a sequence of other_words separated by some number of dots, without any spaces or special characters. *)

let rec dot_other_token () =
  let* n = dots in
  (let* rest = atomic_other_token () in
   return (`Dots n :: rest))
  </> return [ `Dots n ]

and atomic_other_token () =
  let* atom = other_word in
  (let* rest = dot_other_token () in
   return (`Atom atom :: rest))
  </> return [ `Atom atom ]

let dot_separated_token : [ `Dots of int | `Atom of string ] list t =
  dot_other_token () </> atomic_other_token ()

(* Check for notation parts that are reserved words or single underscores. *)
let get_reserved_word = function
  | "let" -> Some Let
  | "rec" -> Some Rec
  | "in" -> Some In
  | "axiom" -> Some Axiom
  | "def" -> Some Def
  | "and" -> Some And
  | "echo" -> Some Echo
  | "synth" -> Some Synth
  | "quit" -> Some Quit
  | "match" -> Some Match
  | "return" -> Some Return
  | "sig" -> Some Sig
  | "data" -> Some Data
  | "codata" -> Some Codata
  | "notation" -> Some Notation
  | "import" -> Some Import
  | "export" -> Some Export
  | "solve" -> Some Solve
  | "split" -> Some Split
  | "show" -> Some Show
  | "display" -> Some Display
  | "option" -> Some Option
  | "undo" -> Some Undo
  | "section" -> Some Section
  | "end" -> Some End
  | "_" -> Some Underscore
  | _ -> None

let is_single_reserved_word = function
  | [ `Atom str ] -> get_reserved_word str
  | _ -> None

let rec contains_reserved_word = function
  | [] -> false
  | `Dots _ :: parts -> contains_reserved_word parts
  | `Atom str :: parts -> Option.is_none (get_reserved_word str) && contains_reserved_word parts

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
      if contains_reserved_word parts then fatal ~loc Parse_error
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
            | _ -> fatal ~loc Parse_error)
        (* Simple constructor *)
        | [ `Atom con; `Dots 1 ] when atomic_ident con -> Constr (con, [])
        (* Higher constructor with multiple suffixes *)
        | `Atom con :: `Dots 2 :: rest when atomic_ident con ->
            let _ =
              match get_higher_parts rest with
              | Some (parts, true) -> Constr (con, parts)
              | _ -> fatal ~loc Parse_error in
            fatal ~loc (Unimplemented "higher constructors")
        (* Higher constructor with single suffix *)
        | [ `Atom con; `Dots 1; `Atom pbij; `Dots 1 ] when atomic_ident con ->
            let _ = Constr (con, String.fold_right (fun c s -> String.make 1 c :: s) pbij []) in
            fatal ~loc (Unimplemented "higher constructors")
        (* Identifier *)
        | _ -> (
            match get_ident parts with
            | Some id -> Ident id
            | None -> fatal ~loc Parse_error))

let other : Token.t t =
  let* rng, parts = located dot_separated_token in
  return (canonicalize (Range.convert rng) parts)

(* Finally, a token is either a quoted string, a single-character operator, an operator of special ASCII symbols, or something else.  Unlike the built-in 'lexer' function, we include whitespace *after* the token, so that we can save comments occurring after any code. *)
let token : Located_token.t t =
  (let* loc, tok =
     located (hole </> quoted_string </> onechar_op </> superscript </> ascii_op </> other) in
   let* ws = whitespace in
   return (loc, (tok, ws)))
  </> located (expect_end (Eof, []))

(* This means we need a separate combinator to parse any initial whitespace.   *)
let bof : Located_token.t t =
  let* ws = whitespace in
  located (return (Bof, ws))

module Parser = struct
  include Basic.Parser

  (* This is how we make the lexer to plug into the parser. *)
  let start : t = make_partial Position.start `None bof
  let restart (lex : t) : t = make_partial (position lex) `None token |> transfer_lookahead lex
end

module Single_token = struct
  module Basic = Token_parser.Make (Unit) (Token_whitespace) (Token_whitespace) (Unit)
  open Basic

  let token : Token_whitespace.t t = step "token" (fun state _ tok -> Some (tok, state))

  module Parser = struct
    include Basic.Parser

    let start : t =
      make ()
        ((* bof *)
         let* _ = token in
         token)
  end
end

module Lex_and_parse_single =
  Parse_with_lexer.Make_utf8 (Unit) (Token_whitespace) (Token_whitespace) (Unit) (Parser)
    (Single_token.Parser)

let single str =
  (* The lexer performs Range effects, so we have to set up handlers for those. *)
  let env : Range.Data.t =
    { source = `String { content = str; title = None }; length = Int64.of_int (String.length str) }
  in
  Range.run ~env @@ fun () ->
  let open Lex_and_parse_single in
  let p = run_on_string str (make Parser.start Single_token.Parser.start) in
  if has_succeeded p then
    let tok, ws = final p in
    if ws = [] then Some tok else None
  else None
