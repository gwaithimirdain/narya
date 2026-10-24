(* This state module tracks user-configurable display states.  These are set by command-line flags or by the "display" command which is out-of-band, i.e. doesn't appear in files and is instead issued by the user interactively or through proof general. *)

type chars = [ `Unicode | `ASCII ]
type metas = [ `Anonymous | `Numbered ]
type argstyle = [ `Spaces | `Parens ]
type spacing = [ `Wide | `Narrow ]
type show = [ `Show | `Hide ]
type holes = [ `With_number | `Without_number ]

(* How to display let-bound variables and holes (which are implemented as metavariables) when they appear in a context other than their own, e.g. after substitution.  With `Names, we display them by name, abbreviating the bindings of the variables in their context by an ellipsis, as in "let only … in x".  With `Environments, we display those bindings in full, but still the name in the body.  With `Definitions, we also display their definitions (if any) instead of their names, including when they appear in their own context. *)
type lets = [ `Names | `Environments | `Definitions ]

let string_of_lets : lets -> string = function
  | `Names -> "names"
  | `Environments -> "environments"
  | `Definitions -> "definitions"

type values = [ `Unicode | `ASCII | `Show | `Hide ]
type 'a toggle = [ `Set of 'a | `Toggle ]

let to_string : values -> string = function
  | `Unicode -> "unicode"
  | `ASCII -> "ASCII"
  | `Show -> "on"
  | `Hide -> "off"

module Config = struct
  type t = {
    chars : chars;
    metas : metas;
    argstyle : argstyle;
    spacing : spacing;
    holes : holes;
    lets : lets;
    implicits : show;
    unique_keys : show;
    (* Degeneracies that are iterated reflexivities are displayed with iterated names, like "refl (refl x)" or "Id (Id X)", when the number of iterations is at most this value, and with a superscript otherwise. *)
    degeneracy_names : int;
    variables : string list;
  }
end

let default : Config.t =
  {
    chars = `Unicode;
    metas = `Numbered;
    argstyle = `Spaces;
    spacing = `Wide;
    holes = `Without_number;
    lets = `Names;
    implicits = `Hide;
    unique_keys = `Hide;
    degeneracy_names = 1;
    variables = [ "𝑥"; "𝑦"; "𝑧"; "𝑤"; "𝑢"; "𝑣" ];
  }

module State = Util.State.Make (Config)

let () =
  State.register_printer (function
    | `Get -> Some "unhandled Display get effect"
    | `Set _ -> Some "unhandled Display set effect")

(* *)
let chars () = (State.get ()).chars
let metas () = (State.get ()).metas
let argstyle () = (State.get ()).argstyle
let spacing () = (State.get ()).spacing
let implicits () = (State.get ()).implicits
let unique_keys () = (State.get ()).unique_keys
let holes () = (State.get ()).holes
let lets () = (State.get ()).lets
let variables () = (State.get ()).variables
let degeneracy_names () = (State.get ()).degeneracy_names

let alt_char uni asc =
  match (State.get ()).chars with
  | `Unicode -> uni
  | `ASCII -> asc

let get = State.get
let run = State.run
let modify = State.modify

let modify_chars chars =
  let s = State.get () in
  let chars =
    match (chars, s.chars) with
    | `Set x, _ -> x
    | `Toggle, `Unicode -> `ASCII
    | `Toggle, `ASCII -> `Unicode in
  State.set { s with chars };
  chars

let modify_implicits im =
  let s = State.get () in
  let implicits =
    match (im, s.implicits) with
    | `Set x, _ -> x
    | `Toggle, `Show -> `Hide
    | `Toggle, `Hide -> `Show in
  State.set { s with implicits };
  implicits

let modify_lets (l : [ `Set of lets | `Cycle ]) =
  let s = State.get () in
  let lets =
    match (l, s.lets) with
    | `Set x, _ -> x
    | `Cycle, `Names -> `Environments
    | `Cycle, `Environments -> `Definitions
    | `Cycle, `Definitions -> `Names in
  State.set { s with lets };
  lets

let modify_unique_keys uk =
  let s = State.get () in
  let unique_keys =
    match (uk, s.unique_keys) with
    | `Set x, _ -> x
    | `Toggle, `Show -> `Hide
    | `Toggle, `Hide -> `Show in
  State.set { s with unique_keys };
  unique_keys

(* For now, we hardcode this. *)
let columns () = 75
