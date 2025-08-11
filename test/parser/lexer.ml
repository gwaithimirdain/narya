open Testutil
open Lex

let () =
  Core.Reporter.run ~fatal:(fun _ -> raise (Failure "fatal error")) ~emit:(fun _ -> ()) @@ fun () ->
  Parser.Range.run ~env:{ source = `String { title = None; content = "" }; length = 0L }
  @@ fun () ->
  assert (lex "a b c" = [ (Ident [ "a" ], []); (Ident [ "b" ], []); (Ident [ "c" ], []) ]);
  assert (lex "A->C" = [ (Ident [ "A" ], []); (Arrow, []); (Ident [ "C" ], []) ]);
  assert (lex "A→C" = [ (Ident [ "A" ], []); (Arrow, []); (Ident [ "C" ], []) ]);

  assert (
    lex "(A\u{21A6}C0) .d"
    = [
        (LParen, []);
        (Ident [ "A" ], []);
        (Mapsto, []);
        (Ident [ "C0" ], []);
        (RParen, []);
        (Field ("d", []), []);
      ]);

  assert (
    lex "th(ns24$#*430-}aqo0[eouOEU){OE)(@@!()#"
    = [
        (Ident [ "th" ], []);
        (LParen, []);
        (Ident [ "ns24" ], []);
        (Op "$#*", []);
        (Ident [ "430" ], []);
        (Op "-", []);
        (RBrace, []);
        (Ident [ "aqo0" ], []);
        (LBracket, []);
        (Ident [ "eouOEU" ], []);
        (RParen, []);
        (LBrace, []);
        (Ident [ "OE" ], []);
        (RParen, []);
        (LParen, []);
        (Op "@@!", []);
        (LParen, []);
        (RParen, []);
        (Op "#", []);
      ]);

  assert (
    lex "this is ` a line comment\n  starting another \"line\""
    = [
        (Ident [ "this" ], []);
        (Ident [ "is" ], [ `Line " a line comment" ]);
        (Ident [ "starting" ], []);
        (Ident [ "another" ], []);
        (String "line", []);
      ]);

  assert (
    lex
      "this is {` a block \n comment spanning \n multiple lines `} ` with a line comment\n and_more-code"
    = [
        (Ident [ "this" ], []);
        ( Ident [ "is" ],
          [ `Block " a block \n comment spanning \n multiple lines "; `Line " with a line comment" ]
        );
        (Ident [ "and_more" ], []);
        (Op "-", []);
        (Ident [ "code" ], []);
      ]);

  assert (
    lex "block comments {` can contain ` line comments \n and {` nest `} arbitrarily `} \n see?"
    = [
        (Ident [ "block" ], []);
        ( Ident [ "comments" ],
          [ `Block " can contain ` line comments \n and {` nest `} arbitrarily "; `Newlines 1 ] );
        (Ident [ "see" ], []);
        (Hole None, []);
      ]);

  assert (
    lex "hole ¿ with ! contents ʔ"
    = [ (Ident [ "hole" ], []); (Hole (Some [ " with "; " contents " ]), []) ]);

  assert (
    lex "hole ¿ with ! more ! contents ʔ"
    = [ (Ident [ "hole" ], []); (Hole (Some [ " with "; " more "; " contents " ]), []) ]);

  assert (
    lex "hole ¿ containing ` ! comments ʔ"
    = [ (Ident [ "hole" ], []); (Hole (Some [ " containing ` "; " comments " ]), []) ]);

  assert (
    lex "hole ¿ containing {` ! `} comment ʔ"
    = [ (Ident [ "hole" ], []); (Hole (Some [ " containing {` "; " `} comment " ]), []) ]);

  assert (lex "hole ` ¿ commented ʔ" = [ (Ident [ "hole" ], [ `Line " ¿ commented ʔ" ]) ]);

  assert (
    lex "block comments {` nest `{` even after `} backquotes `} see?"
    = [
        (Ident [ "block" ], []);
        (Ident [ "comments" ], [ `Block " nest `{` even after `} backquotes " ]);
        (Ident [ "see" ], []);
        (Hole None, []);
      ]);

  assert (
    lex "block comments {`} can start with a lbrace `} see?"
    = [
        (Ident [ "block" ], []);
        (Ident [ "comments" ], [ `Block "} can start with a lbrace " ]);
        (Ident [ "see" ], []);
        (Hole None, []);
      ]);

  assert (
    lex "block ` comments {` don't start in \n line comments"
    = [
        (Ident [ "block" ], [ `Line " comments {` don't start in " ]);
        (Ident [ "line" ], []);
        (Ident [ "comments" ], []);
      ]);

  assert (
    lex "block \"comments {` don't start in\" strings"
    = [
        (Ident [ "block" ], []); (String "comments {` don't start in", []); (Ident [ "strings" ], []);
      ]);

  assert (
    lex "block {` comment `{{` nested ``} done `} over"
    = [ (Ident [ "block" ], [ `Block " comment `{{` nested ``} done " ]); (Ident [ "over" ], []) ]);

  assert (lex "  initial space" = [ (Ident [ "initial" ], []); (Ident [ "space" ], []) ]);

  assert (
    lex "Block comments {` can end the file `}"
    = [ (Ident [ "Block" ], []); (Ident [ "comments" ], [ `Block " can end the file " ]) ]);

  assert (nolex "Unterminated {` block comment" = [ ("any character", None) ]);

  assert (
    lex "let x := a in b : coo"
    = [
        (Let, []);
        (Ident [ "x" ], []);
        (Coloneq, []);
        (Ident [ "a" ], []);
        (In, []);
        (Ident [ "b" ], []);
        (Colon, []);
        (Ident [ "coo" ], []);
      ]);

  assert (lex "" = []);
  assert (lexbof "" = [ (Bof, []) ]);
  assert (lexbof " " = [ (Bof, []) ]);
  assert (lexbof "\n" = [ (Bof, [ `Newlines 1 ]) ]);
  assert (lexbof "` line comment\n" = [ (Bof, [ `Line " line comment" ]) ]);
  assert (lexbof "` line comment" = [ (Bof, [ `Line " line comment" ]) ]);
  assert (lex "x^^(1-2)" = [ (Ident [ "x" ], []); (Superscript "1-2", []) ]);

  assert (
    lex "(x^^(1-2))" = [ (LParen, []); (Ident [ "x" ], []); (Superscript "1-2", []); (RParen, []) ]);

  assert (lex "x ^ y" = [ (Ident [ "x" ], []); (Op "^", []); (Ident [ "y" ], []) ]);
  assert (lex "x⁽¹⁻²⁾" = [ (Ident [ "x" ], []); (Superscript "1-2", []) ]);

  assert (lex "x⁽¹⁾⁽²⁾" = [ (Ident [ "x" ], []); (Superscript "1", []); (Superscript "2", []) ])
