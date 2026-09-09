type t = {
  wslparen : Whitespace.t list;
  names : (string option * Whitespace.t list) list;
  wscolon : Whitespace.t list;
  modality : (string * Whitespace.t list) Asai.Range.located list;
  wsbar : Whitespace.t list;
  ty : Notation.wrapped_parse;
  wsrparen : Whitespace.t list;
}
