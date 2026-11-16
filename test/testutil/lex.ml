open Fparse
open Parser

(* To test the lexer, we hook it up with a trivial parser that just produces a list of tokens. *)

module Token_list = struct
  type t = Lexer.Token_whitespace.t list
end

module Parse_tokens = struct
  module Basic = Token_parser.Make (Unit) (Lexer.Token_whitespace) (Token_list) (Unit)
  open Basic

  let token : Lexer.Token_whitespace.t t = step "token" (fun state _ tok -> Some (tok, state))

  let start : Token_list.t t =
    let* toks = zero_or_more token in
    expect_end toks
end

let trylex str =
  Parser.Lexer.Specials.run @@ fun () ->
  Parse_tokens.Basic.run (Lexer.tokens str) () Parse_tokens.start

let lex str =
  match trylex str with
  | Success toks -> List.tl toks
  | _ -> raise (Failure ("Lexing failed of " ^ str))

let nolex str =
  match trylex str with
  | Failed_syntax _ -> ()
  | _ -> raise (Failure ("Lexing succeeded of " ^ str))

let lexbof str =
  match trylex str with
  | Success toks -> toks
  | _ -> raise (Failure ("Lexing failed of " ^ str))
