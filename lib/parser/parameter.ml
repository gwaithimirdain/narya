(* A group of parameters of a definition or axiom, in parentheses, or in braces if they are implicit. *)
type t = {
  implicit : [ `Explicit | `Implicit ];
  wslparen : Whitespace.t list;
  names : (string option * Whitespace.t list) list;
  wscolon : Whitespace.t list;
  modality : (string * Whitespace.t list) Asai.Range.located list;
  wsbar : Whitespace.t list;
  ty : Notation.wrapped_parse;
  wsrparen : Whitespace.t list;
}
