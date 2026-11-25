open Core
open Origin
open Parser

(* The range of each parsed command runs from the start of its first token to the end of its last one: it doesn't include the whitespace and comments after the command, nor the lookahead token that the parser needed in order to know that the command had ended.  Here we parse (without executing) a sequence of commands and check the text that each range covers. *)

let ranges (content : string) : string list =
  let slice loc =
    match loc with
    | Some loc ->
        let s = Asai.Range.begin_offset loc and e = Asai.Range.end_offset loc in
        String.sub content s (e - s)
    | None -> "(none)" in
  let rec go p src acc =
    let loc, cmd = Command.Parse.final_located p in
    match cmd with
    | Eof ->
        assert (loc = None);
        List.rev acc
    | Bof _ ->
        let p, src = Command.Parse.restart_parse p src in
        go p src (("Bof:" ^ slice loc) :: acc)
    | _ ->
        let p, src = Command.Parse.restart_parse p src in
        go p src (slice loc :: acc) in
  let p, src = Command.Parse.start_parse (`String { title = None; content } : Asai.Range.source) in
  go p src []

let () =
  Parser.Lexer.Specials.run @@ fun () ->
  Origin.run @@ fun () ->
  Origin.with_file ~holes_allowed:true (File.make (`Other "command_ranges")) @@ fun () ->
  Reporter.run ~emit:Reporter.display
    ~mortal:(fun d ->
      Reporter.display d;
      raise (Failure "Parse failure"))
    ~fatal:(fun _ d ->
      Reporter.display d;
      raise (Failure "Parse failure"))
  @@ fun () ->
  (* Commands ending with a term, where the parser has to look at the next token. *)
  assert (
    ranges "axiom A : Type\ndef a : A ≔ b\necho a b\n"
    = [ "Bof:"; "axiom A : Type"; "def a : A ≔ b"; "echo a b" ]);
  (* Comments after a command, and before the first one, are outside the ranges. *)
  assert (
    ranges
      "` initial comment\naxiom A : Type ` line comment\n{` block\n\   comment `}\ndef a : A ≔ b {` block comment `}\n\necho a ` final comment\n"
    = [ "Bof:"; "axiom A : Type"; "def a : A ≔ b"; "echo a" ]);
  (* Commands ending with a fixed token, where the parser doesn't look at the next token. *)
  assert (
    ranges "section s ≔\n  axiom A : Type\nend\naxiom B : Type"
    = [ "Bof:"; "section s ≔"; "axiom A : Type"; "end"; "axiom B : Type" ]);
  (* A command spanning several lines. *)
  assert (
    ranges "def f (x : A)\n  : A\n  ≔ x\n\n` done\n" = [ "Bof:"; "def f (x : A)\n  : A\n  ≔ x" ]);
  (* Bof is empty, and at the first token after any initial comments. *)
  let content = "  ` comment\n  axiom A : Type\n" in
  let p, _ = Command.Parse.start_parse (`String { title = None; content } : Asai.Range.source) in
  match Command.Parse.final_located p with
  | Some bof, Bof _ -> assert (Asai.Range.begin_offset bof = 14 && Asai.Range.end_offset bof = 14)
  | _ -> assert false
