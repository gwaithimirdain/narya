(* This state module tracks user-configurable display states.  These are set by command-line flags or by the "display" command which is out-of-band, i.e. doesn't appear in files and is instead issued by the user interactively or through proof general. *)

type chars = [ `Unicode | `ASCII ]
type metas = [ `Anonymous | `Numbered ]
type argstyle = [ `Spaces | `Parens ]
type spacing = [ `Wide | `Narrow ]
type show = [ `Show | `Hide ]
type holes = [ `With_number | `Without_number ]
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
    implicits : show;
    unique_keys : show;
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
    implicits = `Hide;
    unique_keys = `Hide;
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
let variables () = (State.get ()).variables

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
