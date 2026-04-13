open Core
open Reporter

type colon = [ `Single of string | `Double of string ]

type t =
  (* A Field is an identifier starting with a period, broken into a list of components by internal periods, and with the first component stored separately.  The later components are only used to indicate the partial bijection identifying an instance of a "higher" field of a higher codatatype.  Thus for a record or ordinary codatatype the list is empty.  *)
  | Field of string * string list (* Starting with . *)
  | Constr of string * string list (* Ending with . *)
  | LParen (* ( *)
  | RParen (* ) *)
  | LBracket (* [ *)
  | RBracket (* ] *)
  | LBrace (* { *)
  | RBrace (* } *)
  | Hole of {
      number : string option; (* Prefix label ⁇n, if present *)
      contents : string option; (* None means ?, Some means ¿ ... ʔ with delimiters included *)
    }
  | GeldedQuery (* ʔ *)
  | DblQuery (* ⁇ *)
  | Arrow (* Both -> and → *)
  | DblArrow (* Both => and ⇒ *)
  | Mapsto (* Both |-> and ↦ *)
  | DblMapsto (* Both |=> and ⤇ *)
  | Colon of colon (* : or ∷, perhaps with a modal suffix, where :: is the same as ∷. *)
  | Coloneq (* Both := and ≔ *)
  | DblColoneq (* Both ::= and ⩴ *)
  | Pluseq (* Both += and ⩲ *)
  | Dot (* . *)
  | Ellipsis (* ... and … *)
  | String of string (* Double-quoted *)
  | Underscore (* _ *)
  | And
  | Axiom
  | Codata
  | Data
  | Def
  | Display
  | Echo
  | End
  | Export
  | Import
  | Chdir
  | In
  | Let
  | Match
  | Notation
  | Option
  | Quit
  | Rec
  | Return
  | Section
  | Fmt
  | Show
  | Sig
  | Solve
  | Split
  | Synth
  | Undo
  | Op of string (* Sequence of common ASCII symbols, other than : := ::= += -> |-> |=> etc. *)
  (* Alphanumeric/unicode other than common ASCII symbols and above single-token characters, with dots and underscores occuring only internally, and each dot-separated piece being nonempty.  Those not containing any dots could be local variable names (with one dot, they could be a face of a cube variable), and those consisting entirely of digits could be numerals.  We can't separate these out at lexing time into those that are parts of mixfix notations and those that are potential identifiers, since the mixfix notations in scope change as we go through a file. *)
  | Ident of string list
  | Superscript of string
  | Invalid_superscript of string
  | Bof
  | Eof

let compare : t -> t -> int = compare

(* All (or at least most) of the Unicode superscript characters, their code points, and the corresponding ASCII characters.  This is digits, lowercase Roman letters, parentheses, and plus, minus, and equals signs. *)
let supers =
  [|
    ("⁰", 0x2070, '0');
    ("¹", 0xb9, '1');
    ("²", 0xb2, '2');
    ("³", 0xb3, '3');
    ("⁴", 0x2074, '4');
    ("⁵", 0x2075, '5');
    ("⁶", 0x2076, '6');
    ("⁷", 0x2077, '7');
    ("⁸", 0x2078, '8');
    ("⁹", 0x2079, '9');
    ("ᵃ", 0x1d43, 'a');
    ("ᵇ", 0x1d47, 'b');
    ("ᶜ", 0x1d9c, 'c');
    ("ᵈ", 0x1d48, 'd');
    ("ᵉ", 0x1d49, 'e');
    ("ᶠ", 0x1da0, 'f');
    ("ᵍ", 0x1d4d, 'g');
    ("ʰ", 0x2b0, 'h');
    ("ⁱ", 0x2071, 'i');
    ("ʲ", 0x2b2, 'j');
    ("ᵏ", 0x1d4f, 'k');
    ("ˡ", 0x2e1, 'l');
    ("ᵐ", 0x1d50, 'm');
    ("ⁿ", 0x207f, 'n');
    ("ᵒ", 0x1d52, 'o');
    ("ᵖ", 0x1d56, 'p');
    ("𐞥", 0x107a5, 'q');
    ("ʳ", 0x2b3, 'r');
    ("ˢ", 0x2e2, 's');
    ("ᵗ", 0x1d57, 't');
    ("ᵘ", 0x1d58, 'u');
    ("ᵛ", 0x1d5b, 'v');
    ("ʷ", 0x2b7, 'w');
    ("ˣ", 0x2e3, 'x');
    ("ʸ", 0x2b8, 'y');
    ("ᶻ", 0x1dbb, 'z');
    ("⁻", 0x207b, '-');
    (* ("⁽", 0x207d, '('); *)
    (* ("⁾", 0x207e, ')'); *)
    (* ("⁺", 0x207a, '+'); *)
    (* ("⁼", 0x207c, '='); *)
  |]

let super_strings = Array.map (fun (x, _, _) -> x) supers
let super_uchars = Array.map (fun (_, c, _) -> Uchar.of_int c) supers
let unsupers = Array.map (fun (_, _, s) -> s) supers
let super_lparen_uchar = Uchar.of_int 0x207d
let super_rparen_uchar = Uchar.of_int 0x207e
let super_lparen_string = "⁽"
let super_rparen_string = "⁾"

(* Convert a string of ASCII characters to a corresponding Unicode superscript. *)
let to_super (s : string) : string =
  let b = Buffer.create 10 in
  String.iter
    (fun c ->
      match Array.find_index (fun x -> x = c) unsupers with
      | Some i -> Buffer.add_string b super_strings.(i)
      | None -> fatal (Anomaly "character has no superscript version"))
    s;
  Buffer.contents b

(* Convert a Unicode superscript to a corresponding string of ASCII characters. *)
let of_super (s : string) : string =
  let b = Buffer.create 10 in
  let rec of_super n =
    if n >= String.length s then Buffer.contents b
    else
      let dec = String.get_utf_8_uchar s n in
      if Uchar.utf_decode_is_valid dec then (
        let len = Uchar.utf_decode_length dec in
        let c = Uchar.utf_decode_uchar dec in
        (match Array.find_index (fun x -> x = c) super_uchars with
        | Some i -> Buffer.add_char b unsupers.(i)
        | None -> fatal (Anomaly "character is not a superscript"));
        of_super (n + len))
      else fatal Encoding_error in
  of_super 0

let to_string = function
  | Field (f, strs) ->
      if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
        "." ^ f ^ ".." ^ String.concat "." strs
      else "." ^ f ^ "." ^ String.concat "" strs
  | Constr (c, strs) ->
      if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
        c ^ ".." ^ String.concat "." strs ^ "."
      else c ^ "." ^ String.concat "" strs ^ "."
  | LParen -> "("
  | RParen -> ")"
  | LBracket -> "["
  | RBracket -> "]"
  | LBrace -> "{"
  | RBrace -> "}"
  | Hole { number; contents } ->
      Option.fold ~some:(fun n -> "⁇" ^ n) ~none:"" number ^ Option.value ~default:"?" contents
  | GeldedQuery -> "ʔ"
  | DblQuery -> "⁇"
  | Arrow -> Display.alt_char "→" "->"
  | DblArrow -> Display.alt_char "⇒" "=>"
  | Mapsto -> Display.alt_char "↦" "|->"
  | DblMapsto -> Display.alt_char "⤇" "|=>"
  | Colon (`Single str) -> ":" ^ str
  | Colon (`Double str) -> if str = "" then Display.alt_char "∷" "::" else "∷" ^ str
  | Coloneq -> Display.alt_char "≔" ":="
  | DblColoneq -> Display.alt_char "⩴" "::="
  | Pluseq -> Display.alt_char "⩲" "+="
  | Dot -> "."
  | Ellipsis -> Display.alt_char "…" "..."
  | String s -> "\"" ^ s ^ "\""
  | Underscore -> "_"
  | Axiom -> "axiom"
  | Def -> "def"
  | And -> "and"
  | Echo -> "echo"
  | Synth -> "synth"
  | Quit -> "quit"
  | Match -> "match"
  | Return -> "return"
  | Sig -> "sig"
  | Data -> "data"
  | Codata -> "codata"
  | Notation -> "notation"
  | Import -> "import"
  | Chdir -> "chdir"
  | Export -> "export"
  | Solve -> "solve"
  | Split -> "split"
  | Show -> "show"
  | Display -> "display"
  | Option -> "option"
  | Undo -> "undo"
  | Section -> "section"
  | Fmt -> "fmt"
  | End -> "end"
  | Let -> "let"
  | Rec -> "rec"
  | In -> "in"
  | Op s -> s
  | Ident s -> String.concat "." s
  | Superscript s -> to_super s
  | Invalid_superscript s -> to_super s
  | Bof -> "BOF"
  | Eof -> "EOF"

(* Given a token, create a constant pretty-printer that prints that token. *)
let pp tok = PPrint.utf8string (to_string tok)
