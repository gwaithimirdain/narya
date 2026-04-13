type t = {
  wslparen : Whitespace.t list;
  names : (string option * Whitespace.t list) list;
  colon : Token.colon Asai.Range.located;
  wscolon : Whitespace.t list;
  ty : Notation.wrapped_parse;
  wsrparen : Whitespace.t list;
}
