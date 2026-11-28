open Util
open Core
open Reporter
open Notation
open PPrint
open Print
module StringMap = Map.Make (String)

(* A user notation pattern is a nonempty sequence of operator symbols and variable names.  There must be at least one operator symbol, and any two variable names must be separated by at least one symbol.  It is left-closed if the first element is an operator symbol and left-open if the first element is a variable, and similarly for right-open and -closed and the last element.  The two opennesses in turn determine whether it is infix, prefix, postfix, or outfix, but not its associativity or tightness.  *)

module Pattern = struct
  (* A variable position of a pattern, or "slot", is usually a single variable.  It can also be a "typed binder" "(x : A)" for a notation that binds a variable, which is a single term position in the notation, but at which the user can write either an ascribed variable "(x : A)", binding x with type A, or just a term A, binding an anonymous variable with type A, as in a pi-type.  A typed binder can also be modal, "(x :μ| A)", in which case an ascribed variable at that position must have the same modality.  For a typed binder we remember the whitespace after the left parenthesis, the variable, the colon, each name in the modality, the bar (if the modality is nonempty), and the type; that after the right parenthesis is stored along with the slot as for any other one. *)
  type slot =
    | Plain of string
    | Typed of {
        var : string;
        ty : string;
        wslparen : Whitespace.t list;
        wsvar : Whitespace.t list;
        wscolon : Whitespace.t list;
        modality : (string * Whitespace.t list) list;
        wsbar : Whitespace.t list;
        wsty : Whitespace.t list;
      }

  (* The variable names introduced by a slot. *)
  let slot_names : slot -> string list = function
    | Plain x -> [ x ]
    | Typed { var; ty; _ } -> [ var; ty ]

  (* This type ensures statically that all the invariants mentioned above must hold, and is parametrized by the left- and right-openness.
     Each symbol or slot is stored along with the type of space following it, except for those that occur last. *)
  type (_, _) t =
    | Op_nil : Token.t * Whitespace.t list -> (closed, closed) t
    (* If a pattern ends with a slot, that slot must be immediately preceded by an operator symbol, so we include that in the corresponding "nil". *)
    | Var_nil :
        (Token.t * space * Whitespace.t list) * (slot * Whitespace.t list)
        -> (closed, 's opn) t
    | Op : (Token.t * space * Whitespace.t list) * ('left, 'right) t -> (closed, 'right) t
    | Var : (slot * space * Whitespace.t list) * (closed, 'right) t -> ('s opn, 'right) t

  (* List the slots of a pattern. *)
  let rec slots : type left right. (left, right) t -> slot list = function
    | Op_nil _ -> []
    | Var_nil (_, (x, _)) -> [ x ]
    | Op (_, pat) -> slots pat
    | Var ((x, _, _), pat) -> x :: slots pat

  let inner_symbols : type left right.
      (left, right) t ->
      [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ] =
   fun pat ->
    let rec go : type left right. (left, right) t -> Token.t option list * Token.t = function
      | Op_nil (tok, _) -> ([], tok)
      | Var_nil ((tok, _, _), _) -> ([], tok)
      | Op ((tok, _, _), pat) ->
          let inner, last = go pat in
          (Some tok :: inner, last)
      | Var (_, pat) ->
          let inner, last = go pat in
          (None :: inner, last) in
    match go pat with
    | Some first :: inner, last -> `Multiple (first, inner, last)
    | None :: Some first :: inner, last -> `Multiple (first, inner, last)
    | None :: None :: _, _ -> fatal (Anomaly "two sequential variables in inner_symbols")
    | [ None ], tok | [], tok -> `Single tok

  (* A pattern parametrized only by its right-openness. *)
  type _ right_t = Right : ('left, 'right) t -> 'right right_t

  (* Cons a variable on the left of any pattern, raising an error if that would put two variables next to each other. *)
  let var : type left right s.
      slot * space * Whitespace.t list -> (left, right) t -> (s opn, right) t =
   fun v pat ->
    match pat with
    | Op_nil _ as pat -> Var (v, pat)
    | Var_nil _ as pat -> Var (v, pat)
    | Op (_, _) as pat -> Var (v, pat)
    | _ -> fatal (Invalid_notation_pattern "missing symbol between variables")

  let rec to_string : type left right. (left, right) t -> string = function
    | Op_nil (tok, _) -> Token.to_string tok
    | Var_nil ((tok, _, _), _) -> Token.to_string tok ^ " _"
    | Op ((tok, _, _), rest) -> Token.to_string tok ^ " " ^ to_string rest
    | Var (_, rest) -> "_ " ^ to_string rest
end

(* Print a slot of a pattern the way the user would enter it. *)
let pp_slot : Pattern.slot -> document = function
  | Plain x -> utf8string x
  | Typed { var; ty; wslparen; wsvar; wscolon; modality; wsbar; wsty } ->
      Token.pp LParen
      ^^ pp_ws `None wslparen
      ^^ utf8string var
      ^^ pp_ws `Break wsvar
      ^^ Token.pp Colon
      (* As for modal ascriptions in terms, a single modality name is printed attached to the colon and bar, as is a composite one if all generators are single characters (with its names run together, although we keep any comments between them), while otherwise a composite one is spaced out. *)
      ^^ (match modality with
        | [] -> pp_ws `Nobreak wscolon
        | ([ _ ] | _) when Modal.Modality.one_char () ->
            pp_ws `None wscolon
            ^^ concat_map (fun (m, wsm) -> utf8string m ^^ pp_ws `None wsm) modality
            ^^ Token.pp (Op "|")
            ^^ pp_ws `Nobreak wsbar
        | ms ->
            pp_ws `Nobreak wscolon
            ^^ concat_map (fun (m, wsm) -> utf8string m ^^ pp_ws `Break wsm) ms
            ^^ Token.pp (Op "|")
            ^^ pp_ws `Nobreak wsbar)
      ^^ utf8string ty
      ^^ pp_ws `None wsty
      ^^ Token.pp RParen

(* Print a *pattern* the way the user would enter it in a "notation" command, with quotes around the operator symbols. *)
let pp_pattern : type left right. (left, right) Pattern.t -> document * Whitespace.t list =
 fun pattern ->
  let rec go : type left right.
      (left, right) Pattern.t -> Whitespace.t list option -> document * Whitespace.t list =
   fun pattern prews ->
    match pattern with
    | Var ((x, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ pp_slot x) ^^ ppat, wpat)
    | Var_nil ((op, _, opws), (x, varws)) ->
        ( group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op))
          ^^ group (pp_ws `Break opws ^^ pp_slot x),
          varws )
    | Op ((op, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)) ^^ ppat, wpat)
    | Op_nil (op, ws) -> (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)), ws) in
  go pattern None

(* Like a constant, a user notation is identified by an autonumber scoped by the origin where its "notation" command was executed.  Compiling a prenotation into a notation gives it a *runtime* identity too (an extension constructor, see below), but that one is minted afresh every time we compile, and can't be marshaled; so it is this identity that says when two notations arriving in a scope -- imported along two paths, or unmarshaled from two different compiled files -- are really the same notation.  Like constant identities, it is linked when loading a compiled file. *)

module Id = struct
  open Origin

  type t = Origin.t * int

  let compare : t -> t -> int = compare

  (* Autonumber counters, one per origin. *)
  let counters = Versioned.make ~default:(fun _ -> 0) ~inherit_values:false

  let make () : t =
    let current = Origin.current () in
    let number = Versioned.get counters in
    Versioned.set counters (number + 1);
    (current, number)

  (* Recreate an id with an altered file identifier, as when linking. *)
  let remake f ((o : Origin.t), i) =
    match o with
    | File n -> (Origin.File (f n), i)
    (* A notation defined interactively is never marshaled, so it is never linked either. *)
    | Top -> (o, i)
    | Instant _ -> raise (Failure "User.Id: can't remake interactive notation")
end

(* A user "prenotation" includes all the information from a "notation" command, parsed and validated into a pattern, fixity, and so on, but not yet compiled into a notation tree. *)

type key = [ `Constant of Core.Constant.t | `Constr of Core.Constr.t * int ]

(* An argument of the head in the definition of a notation: either a variable of the pattern, or an abstraction "(x y ↦ b)" of a variable of the pattern over one or more others, which are thereby "binders" of the notation. *)
type arg = Arg of string | Abs of string list * string

let is_abs : arg -> bool = function
  | Abs _ -> true
  | Arg _ -> false

(* The variables of the pattern that are binders. *)
let binders_of_args (args : arg list) : string list =
  List.concat_map
    (function
      | Arg _ -> []
      | Abs (xs, _) -> xs)
    args

type ('left, 'tight, 'right) prenotation_data = {
  id : Id.t;
  name : string;
  fixity : ('left, 'tight, 'right) fixity;
  pattern : ('left, 'right) Pattern.t;
  key : key;
  val_args : arg list;
}

type prenotation = User : ('left, 'tight, 'right) prenotation_data -> prenotation

(* Whereas a user "notation" has been compiled into a notation tree, but remembers the slots from the pattern and the arguments in the definition, so as to implement the necessary permutation and binding. *)

type notation = {
  keys : key list;
  notn : Notation.t;
  pat_slots : Pattern.slot list;
  val_args : arg list;
  inner_symbols : [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ];
}

(* What was written at a binding position of a notation: a variable or underscore, or a parenthesized variable or underscore ascribed to a type, possibly with a modality; or a parenthesized ascription that can't be a binder (with the reason), or something else. *)
type binder_parse =
  | Binder of
      string option * (string Asai.Range.located list Asai.Range.located * wrapped_parse) option
  | Invalid_binder of [ `Implicit | `Multiple | `Not_variable ]
  | Not_binder

(* The global processing function isn't defined until postprocess.ml, but we need it before that here. *)

type global_processor = {
  process :
    'n 'lt 'ls 'rt 'rs.
    (string option, 'n) Bwv.t ->
    ('lt, 'ls, 'rt, 'rs) parse Asai.Range.located ->
    'n Raw.check Asai.Range.located;
  pattern : 'lt 'ls 'rt 'rs. ('lt, 'ls, 'rt, 'rs) parse Asai.Range.located -> Matchpattern.t;
  binder : 'lt 'ls 'rt 'rs. ('lt, 'ls, 'rt, 'rs) parse Asai.Range.located -> binder_parse;
}

let global_processor : global_processor ref =
  ref
    {
      process = (fun _ _ -> fatal (Anomaly "global_processor not set"));
      pattern = (fun _ -> fatal (Anomaly "global_processor not set"));
      binder = (fun _ -> fatal (Anomaly "global_processor not set"));
    }

(* Whether two modality names are the same, once split into generators. *)
let same_modality (m1 : string Asai.Range.located list) (m2 : string list) : bool =
  let split ms =
    List.map (fun (m : string Asai.Range.located) -> m.value) (Modal.Modality.split_names ms) in
  split m1 = split (List.map (Asai.Range.locate_opt None) m2)

(* Interpret what was written at a slot of a notation that is used as a binder: a plain slot must be a variable, possibly ascribed (with any modality), which ascribes the domain of the abstraction.  A typed slot can be an ascribed variable with the slot's modality, or any other term, which is then the type of an anonymous variable; either way the type is an argument rather than the domain of the abstraction. *)
let get_binder (slot : Pattern.slot) (Wrap x : wrapped_parse) :
    string option Asai.Range.located
    * (string Asai.Range.located list Asai.Range.located * wrapped_parse) option =
  match (slot, !global_processor.binder x) with
  | _, Invalid_binder err ->
      fatal ?loc:x.loc
        (Invalid_notation_binding
           (err :> [ `Implicit | `Multiple | `Not_variable | `Modality of string list ]))
  | Plain _, Binder (name, dom) -> ({ value = name; loc = x.loc }, dom)
  | Plain _, Not_binder -> fatal ?loc:x.loc (Invalid_notation_binding `Not_variable)
  | Typed { modality; _ }, Binder (name, Some (m, ty)) ->
      let modality = List.map fst modality in
      if not (same_modality m.value modality) then
        fatal ?loc:x.loc (Invalid_notation_binding (`Modality modality));
      ({ value = name; loc = x.loc }, Some (m, ty))
  | Typed _, (Binder (_, None) | Not_binder) ->
      ({ value = None; loc = x.loc }, Some (Asai.Range.locate_opt None [], Wrap x))

(* Compile a prenotation into a notation.  *)

let make_user : prenotation -> notation =
 fun notn ->
  let open Notation in
  let (User
         (type l t r)
         ({ id = _; name; fixity; pattern; key; val_args } : (l, t, r) prenotation_data)) =
    notn in
  let module New = Make (struct
    type nonrec left = l
    type nonrec tight = t
    type nonrec right = r
  end) in
  let n = (New.User, fixity) in
  let pat_slots = Pattern.slots pattern in
  let binders = binders_of_args val_args in
  let inner_symbols = Pattern.inner_symbols pattern in
  make n
    {
      name;
      (* Convert a user notation pattern to a notation tree.  Note that our highly structured definition of the type of patterns, that enforces invariants statically, means that this function CANNOT FAIL. *)
      tree =
        (* We have to handle the beginning specially, since the start and end of a notation tree are different depending on whether it is left-open or left-closed.  So we have an internal recursive function that handles everything except the first operator symbol. *)
        (let rec go : type left l tight.
             (l, r) Pattern.t -> (tight, left) tree -> (tight, left) tree =
          fun pat n ->
           match pat with
           | Op_nil (tok, _) -> op tok n
           | Var_nil ((tok, _, _), _) -> op tok n
           | Op ((tok, _, _), pat) -> op tok (go pat n)
           | Var (_, Op ((tok, _, _), pat)) -> term tok (go pat n)
           | Var (_, Op_nil (tok, _)) -> term tok n
           | Var (_, Var_nil ((tok, _, _), _)) -> term tok n in
         match pattern with
         | Op_nil (tok, _) -> Closed_entry (eop tok (Done_closed n))
         | Var (_, Op ((tok, _, _), pat)) -> Open_entry (eop tok (go pat (done_open n)))
         | Var (_, Op_nil (tok, _)) -> Open_entry (eop tok (done_open n))
         | Var (_, Var_nil ((tok, _, _), _)) -> Open_entry (eop tok (done_open n))
         | Op ((tok, _, _), pat) -> Closed_entry (eop tok (go pat (Done_closed n)))
         | Var_nil ((tok, _, _), _) -> Closed_entry (eop tok (Done_closed n)));
      processor =
        (fun ctx obs loc ->
          (* Sort the terms written in the slots into those that are arguments (including the types of typed binders) and those that are binders. *)
          let terms, binder_args =
            List.fold_left2
              (fun (terms, binder_args) slot (x : wrapped_parse) ->
                match slot with
                | Pattern.Plain k when List.mem k binders ->
                    (terms, binder_args |> StringMap.add k (get_binder slot x))
                | Plain k -> (terms |> StringMap.add k x, binder_args)
                | Typed { var; ty; _ } -> (
                    match get_binder slot x with
                    | name, Some (_, ty') ->
                        ( terms |> StringMap.add ty ty',
                          binder_args |> StringMap.add var (name, None) )
                    | _, None -> fatal (Anomaly "typed binder without type")))
              (StringMap.empty, StringMap.empty)
              pat_slots
              (List.filter_map
                 (function
                   | Term x -> Some (Wrap x : wrapped_parse)
                   | _ -> None)
                 obs) in
          let process_term : type n.
              (string option, n) Bwv.t -> string -> n Raw.check Asai.Range.located =
           fun ctx k ->
            match StringMap.find_opt k terms with
            | Some (Wrap x) -> !global_processor.process ctx x
            | None -> fatal (Anomaly "not found processing user") in
          (* An abstraction binds its variables in its body, with the given ascriptions if any. *)
          let rec process_abs : type n.
              (string option, n) Bwv.t -> string list -> string -> n Raw.check Asai.Range.located =
           fun ctx xs body ->
            match xs with
            | [] -> process_term ctx body
            | x :: xs -> (
                match StringMap.find_opt x binder_args with
                | Some (name, dom) ->
                    let dom =
                      Option.map
                        (fun (modality, (Wrap dom : wrapped_parse)) ->
                          (modality, !global_processor.process ctx dom))
                        dom in
                    let body = process_abs (Bwv.snoc ctx name.value) xs body in
                    {
                      value =
                        Raw.Lam
                          {
                            name;
                            cube = Asai.Range.locate_opt None `Normal;
                            implicit = `Explicit;
                            dom;
                            body;
                          };
                      (* The binder can come after the body in the notation, so we can't merge their locations; instead we use that of the whole notation. *)
                      loc;
                    }
                | None -> fatal (Anomaly "binder not found processing user")) in
          let process_arg = function
            | Arg k -> process_term ctx k
            | Abs (xs, body) -> process_abs ctx xs body in
          let value =
            match key with
            | `Constant c ->
                let spine =
                  List.fold_left
                    (fun acc k ->
                      let arg = process_arg k in
                      Raw.App
                        ( { value = Synth acc; loc },
                          { value = Some arg.value; loc = arg.loc },
                          Asai.Range.locate_opt None `Explicit ))
                    (Const c) val_args in
                Raw.Synth spine
            | `Constr (c, _) ->
                let args = List.map process_arg val_args in
                Raw.Constr
                  ( { value = c; loc },
                    List.map
                      (fun (arg : _ Raw.check Asai.Range.located) ->
                        (arg, Asai.Range.locate_opt arg.loc `Explicit))
                      args ) in
          { value; loc });
      pattern =
        (fun obs loc ->
          match key with
          | `Constr (c, _) ->
              (* A notation that binds variables can't be a pattern, so all its slots are plain. *)
              if not (List.is_empty binders) then
                fatal ?loc
                  (Parse_error "a notation that binds variables can't be used in a pattern");
              let args =
                Mlist.fold_left2
                  (fun (acc : Matchpattern.t StringMap.t) slot (Wrap x : wrapped_parse) ->
                    match slot with
                    | Pattern.Plain k -> acc |> StringMap.add k (!global_processor.pattern x)
                    | Typed _ -> fatal (Anomaly "typed binder in pattern"))
                  StringMap.empty pat_slots
                  (List.filter_map
                     (function
                       | Term x -> Some (Wrap x : wrapped_parse)
                       | _ -> None)
                     obs) in
              (* A user notation's pattern variables are always ordinary (cube) ones; there is no way to give explicit boundaries for them. *)
              let explicit = function
                | Arg k -> Matchpattern.explicit (StringMap.find k args)
                | Abs _ -> fatal (Anomaly "abstraction in pattern") in
              let (Wrap args) = Vec.of_list_map explicit val_args in
              Matchpattern.Constr ({ value = c; loc }, args)
          | `Constant _ -> fatal ?loc (Parse_error "invalid pattern"));
      (* We define this function inline here so that it can match against the constructor New.User that was generated above by the inline Make functor application.  The only way I can think of to factor this function out (and, for instance, put it in user.ml instead of this file) would be to pass it a first-class module as an argument.  At the moment, that seems like unnecessary complication. *)
      print_term =
        Some
          (fun obs ->
            let rec go : type l r.
                bool -> (l, r) Pattern.t -> observation list -> document * Whitespace.t list =
             fun first pat obs ->
              match (pat, obs) with
              | Op ((op, br, _), pat), Token (op', (wsop, _)) :: obs when op = op' ->
                  let rest, ws = go false pat obs in
                  (Token.pp op ^^ pp_ws br wsop ^^ rest, ws)
              | Op_nil (op, _), [ Token (op', (wsop, _)) ] when op = op' -> (Token.pp op, wsop)
              | Var_nil ((op, opbr, _), _), [ Token (op', (wsop, _)); Term x ] when op = op' ->
                  (* Deal with right-associativity *)
                  let xdoc, xws =
                    match x.value with
                    | Notn ((New.User, _), d) -> go false pattern (args d)
                    | _ -> pp_term x in
                  (Token.pp op ^^ pp_ws opbr wsop ^^ xdoc, xws)
              | Var ((_, br, _), pat), Term x :: obs ->
                  (* Deal with left-associativity *)
                  let xdoc, xws =
                    match (first, x.value) with
                    | true, Notn ((New.User, _), d) -> go true pattern (args d)
                    | _ -> pp_term x in
                  let rest, ws = go false pat obs in
                  (xdoc ^^ pp_ws br xws ^^ rest, ws)
              | _ -> fatal (Anomaly ("invalid notation arguments for user notation: " ^ name)) in
            (* Note the choice here.  "group" means that the whole notation, including associative repetitions, must all fit on one line or all be broken.  Where it is broken depends on the space arguments in the notation, which specify where there are spaces and where breaks are allowed.  "align" says that if it is broken, later lines will line up below the starting point. *)
            let doc, ws = go true pattern obs in
            (align (group doc), ws));
      print_case = None;
      is_case = (fun _ -> false);
    };
  { keys = [ key ]; notn = Wrap n; pat_slots; val_args; inner_symbols }
