open Util
open Core
open Reporter
open Notation
open PPrint
open Print
module StringMap = Map.Make (String)

(* A user notation pattern is a nonempty sequence of operator symbols and variable names.  There must be at least one operator symbol, and any two variable names must be separated by at least one symbol.  It is left-closed if the first element is an operator symbol and left-open if the first element is a variable, and similarly for right-open and -closed and the last element.  The two opennesses in turn determine whether it is infix, prefix, postfix, or outfix, but not its associativity or tightness.  *)

module Pattern = struct
  (* This type ensures statically that all the invariants mentioned above must hold, and is parametrized by the left- and right-openness.
     Each symbol or variable is stored along with the type of space following it, except for those that occur last. *)
  type (_, _) t =
    | Op_nil : Token.t * Whitespace.t list -> (closed, closed) t
    (* If a pattern ends with a variable, that variable must be immediately preceded by an operator symbol, so we include that in the corresponding "nil". *)
    | Var_nil :
        (Token.t * space * Whitespace.t list) * (string * Whitespace.t list)
        -> (closed, 's opn) t
    | Op : (Token.t * space * Whitespace.t list) * ('left, 'right) t -> (closed, 'right) t
    | Var : (string * space * Whitespace.t list) * (closed, 'right) t -> ('s opn, 'right) t

  (* List the variable names used in a pattern. *)
  let rec vars : type left right. (left, right) t -> string list = function
    | Op_nil _ -> []
    | Var_nil (_, (x, _)) -> [ x ]
    | Op (_, pat) -> vars pat
    | Var ((x, _, _), pat) -> x :: vars pat

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
      string * space * Whitespace.t list -> (left, right) t -> (s opn, right) t =
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

(* Print a *pattern* the way the user would enter it in a "notation" command, with quotes around the operator symbols. *)
let pp_pattern : type left right. (left, right) Pattern.t -> document * Whitespace.t list =
 fun pattern ->
  let rec go : type left right.
      (left, right) Pattern.t -> Whitespace.t list option -> document * Whitespace.t list =
   fun pattern prews ->
    match pattern with
    | Var ((x, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ utf8string x) ^^ ppat, wpat)
    | Var_nil ((op, _, opws), (x, varws)) ->
        ( group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op))
          ^^ group (pp_ws `Break opws ^^ utf8string x),
          varws )
    | Op ((op, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)) ^^ ppat, wpat)
    | Op_nil (op, ws) -> (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)), ws) in
  go pattern None

(* A user "prenotation" includes all the information from a "notation" command, parsed and validated into a pattern, fixity, and so on, but not yet compiled into a notation tree. *)

type key = [ `Constant of Core.Constant.t | `Constr of Core.Constr.t * int ]

type ('left, 'tight, 'right) prenotation_data = {
  name : string;
  fixity : ('left, 'tight, 'right) fixity;
  pattern : ('left, 'right) Pattern.t;
  key : key;
  val_vars : string list;
}

type prenotation = User : ('left, 'tight, 'right) prenotation_data -> prenotation

(* Whereas a user "notation" has been compiled into a notation tree, but remembers the variables from the pattern and the definition, so as to implement the necessary permutation. *)

type notation = {
  keys : key list;
  notn : Notation.t;
  pat_vars : string list;
  val_vars : string list;
  inner_symbols : [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ];
}

(* The global processing function isn't defined until postprocess.ml, but we need it before that here. *)

type global_processor = {
  process :
    'n 'lt 'ls 'rt 'rs.
    (string option, 'n) Bwv.t ->
    ('lt, 'ls, 'rt, 'rs) parse Asai.Range.located ->
    'n Raw.check Asai.Range.located;
}

let global_processor : global_processor ref =
  ref { process = (fun _ _ -> fatal (Anomaly "global_processor not set")) }

(* Compile a prenotation into a notation.  *)

let make_user : prenotation -> notation =
 fun notn ->
  let open Notation in
  let (User (type l t r) ({ name; fixity; pattern; key; val_vars } : (l, t, r) prenotation_data)) =
    notn in
  let module New = Make (struct
    type nonrec left = l
    type nonrec tight = t
    type nonrec right = r
  end) in
  let n = (New.User, fixity) in
  let pat_vars = Pattern.vars pattern in
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
          let args =
            List.fold_left2
              (fun acc k -> function
                | (Wrap x : wrapped_parse) ->
                    acc |> StringMap.add k (!global_processor.process ctx x))
              StringMap.empty pat_vars
              (List.filter_map
                 (function
                   | Term x -> Some (Wrap x : wrapped_parse)
                   | _ -> None)
                 obs) in
          let value =
            match key with
            | `Constant c ->
                let spine =
                  List.fold_left
                    (fun acc k ->
                      match StringMap.find_opt k args with
                      | None -> fatal (Anomaly "not found processing user")
                      | Some arg ->
                          Raw.App
                            ( { value = Synth acc; loc },
                              { value = Some arg.value; loc = arg.loc },
                              Asai.Range.locate_opt None `Explicit ))
                    (Const c) val_vars in
                Raw.Synth spine
            | `Constr (c, _) ->
                let args = List.map (fun k -> StringMap.find k args) val_vars in
                Raw.Constr ({ value = c; loc }, args) in
          { value; loc });
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
  { keys = [ key ]; notn = Wrap n; pat_vars; val_vars; inner_symbols }
