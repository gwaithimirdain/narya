open Bwd
open Bwd.Infix
open Util
open Tbwd
open Bwd_extra
open Dim
open Core
open Origin
open Term
open Notation
open Builtins
open Reporter
open Printable
open Range
open Readback
module StringMap = Map.Make (String)

let mktok (tok : Token.t) = Token (tok, ([], None))
let wstok (tok : Token.t) = Either.Left (tok, ([], None))
let sstok (tok : Token.t) (ss : string) = Either.Right ((tok, ([], None)), [ (unlocated ss, []) ])

(* If the head of an application spine is a constant or constructor, and it has an associated notation, and there are enough of the supplied arguments to instantiate the notation, split off that many arguments and return the notation, those arguments permuted to match the order of the pattern variables in the notation, the symbols to intersperse with them, and the remaining arguments. *)
let get_notation head args =
  let open Monad.Ops (Monad.Maybe) in
  let* { keys = _; notn; pat_vars; val_vars; inner_symbols } =
    match head with
    | `Term (Const c) -> Scope.Situation.unparse (`Constant c)
    | `Constr c -> Scope.Situation.unparse (`Constr (c, Bwd.length args))
    (* TODO: Can we associate notations to Fields too? *)
    | _ -> None in
  (* There's probably a more efficient way to do this that doesn't involve converting to and from forwards lists, but this way is more natural and easier to understand, and I think this is unlikely to be a performance bottleneck. *)
  let rec take_labeled labels elts acc =
    match (labels, elts) with
    | [], _ -> return (acc, elts)
    | _ :: _, [] -> None
    | k :: labels, x :: elts -> take_labeled labels elts (acc |> StringMap.add k x) in
  let* first, rest = take_labeled val_vars (Bwd.to_list args) StringMap.empty in
  let first =
    List.map (fun k -> StringMap.find_opt k first <|> Anomaly "not found in get_notation") pat_vars
  in
  (* Constructors don't belong to a function-type, so their notation can't be applied to "more arguments" as a function.  Thus, if there are more arguments leftover, it means that the constructor is being used at a different datatype that takes a different number of arguments, and so the notation shouldn't be applied at all (just as if there were too few arguments). *)
  match (head, rest) with
  | `Constr _, _ :: _ -> None
  | _ -> return (notn, first, inner_symbols, Bwd.of_list rest)

(* Put parentheses around a term. *)
let parenthesize tm =
  unlocated
    (outfix ~notn:Postprocess.parens
       ~inner:(Multiple (wstok LParen, Snoc (Emp, Term tm), wstok RParen)))

let braceize tm =
  unlocated
    (outfix ~notn:Postprocess.braces
       ~inner:(Multiple (wstok LBrace, Snoc (Emp, Term tm), wstok RBrace)))

(* Put them only if they aren't there already *)
let parenthesize_maybe (tm : ('lt, 'ls, 'rt, 'rs) parse located) =
  match tm.value with
  | Notn ((Postprocess.Parens, _), _) -> tm
  | _ -> parenthesize tm

(* A "delayed" result of unparsing that needs only to know the tightness intervals to produce a result. *)
type unparser = {
  unparse :
    'lt 'ls 'rt 'rs.
    ('lt, 'ls) No.iinterval -> ('rt, 'rs) No.iinterval -> ('lt, 'ls, 'rt, 'rs) parse located;
}

let observations_of_symbols :
    unparser list ->
    [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ] ->
    observations =
 fun args inner_symbols ->
  match inner_symbols with
  | `Single tok -> Single (wstok tok)
  | `Multiple (first, inner, last) ->
      Multiple
        ( wstok first,
          fst
            (List.fold_left
               (fun (acc, args) symbol ->
                 match (symbol, args) with
                 | Some tok, _ -> (Snoc (acc, mktok tok), args)
                 | None, tm :: args ->
                     (Snoc (acc, Term (tm.unparse No.Interval.entire No.Interval.entire)), args)
                 | None, [] -> fatal (Anomaly "missing argument in observations_of_symbols"))
               (Emp, args) inner),
          wstok last )

(* Unparse a notation together with all its arguments. *)
let unparse_notation : type left tight right lt ls rt rs.
    (left, tight, right) notation ->
    unparser list ->
    [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ] ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun notn args inner_symbols li ri ->
  let t = tightness notn in
  (* Based on the fixity of the notation, we have to extract the first and/or last argument to treat differently.  In each case except for outfix, we also have to test whether the notation fits in the given tightness interval, and if not, parenthesize it. *)
  match (left notn, right notn) with
  | Open _, Open _ -> (
      match List_extra.split_last args with
      | Some (first :: inner, last) -> (
          let inner = observations_of_symbols inner inner_symbols in
          match (No.Interval.contains li t, No.Interval.contains ri t) with
          | Some left_ok, Some right_ok ->
              let first = first.unparse li (interval_left notn) in
              let last = last.unparse (interval_right notn) ri in
              unlocated (infix ~notn ~first ~inner ~last ~left_ok ~right_ok)
          | _ ->
              let first = first.unparse No.Interval.entire (interval_left notn) in
              let last = last.unparse (interval_right notn) No.Interval.entire in
              let left_ok = No.minusomega_le t in
              let right_ok = No.minusomega_le t in
              parenthesize (unlocated (infix ~notn ~first ~inner ~last ~left_ok ~right_ok)))
      | _ -> fatal (Anomaly "missing arguments unparsing infix"))
  | Closed, Open _ -> (
      match List_extra.split_last args with
      | Some (inner, last) -> (
          let inner = observations_of_symbols inner inner_symbols in
          match No.Interval.contains ri t with
          | Some right_ok ->
              let last = last.unparse (interval_right notn) ri in
              unlocated (prefix ~notn ~inner ~last ~right_ok)
          | _ ->
              let last = last.unparse (interval_right notn) No.Interval.entire in
              let right_ok = No.minusomega_le t in
              parenthesize (unlocated (prefix ~notn ~inner ~last ~right_ok)))
      | _ -> fatal (Anomaly "missing argument unparsing prefix"))
  | Open _, Closed -> (
      match args with
      | first :: inner -> (
          let inner = observations_of_symbols inner inner_symbols in
          match No.Interval.contains li t with
          | Some left_ok ->
              let first = first.unparse li (interval_left notn) in
              unlocated (postfix ~notn ~first ~inner ~left_ok)
          | _ ->
              let first = first.unparse No.Interval.entire (interval_left notn) in
              let left_ok = No.minusomega_le t in
              parenthesize (unlocated (postfix ~notn ~first ~inner ~left_ok)))
      | _ -> fatal (Anomaly "missing argument unparsing postfix"))
  | Closed, Closed ->
      let inner = observations_of_symbols args inner_symbols in
      unlocated (outfix ~notn ~inner)

(* Unparse a variable name. *)
let unparse_var : type lt ls rt rs. string -> (lt, ls, rt, rs) parse located =
 fun x -> unlocated (Ident ([ x ], []))

let unparse_var_with_implicitness : type lt ls rt rs.
    string * [ `Explicit | `Implicit ] -> (lt, ls, rt, rs) parse located = function
  | x, `Explicit -> unlocated (Ident ([ x ], []))
  | x, `Implicit -> braceize (unlocated (Ident ([ x ], [])))

(* Unparse a Bwd of variables to occur in an iterated abstraction.  If there is more than one variable, the result is an "application spine".  Can occur in any tightness interval that contains +ω. *)
let rec unparse_abs : type li ls ri rs.
    (string * [ `Explicit | `Implicit ]) Bwd.t ->
    (li, ls) No.iinterval ->
    (li, ls, No.plus_omega) No.lt ->
    (ri, rs, No.plus_omega) No.lt ->
    (li, ls, ri, rs) parse located =
 fun xs li left_ok right_ok ->
  match xs with
  | Emp -> fatal (Anomaly "missing abstractions")
  | Snoc (Emp, x) -> unparse_var_with_implicitness x
  | Snoc (xs, x) ->
      let fn = unparse_abs xs li left_ok (No.le_refl No.plus_omega) in
      let arg = unparse_var_with_implicitness x in
      unlocated (App { fn; arg; left_ok; right_ok })

let rec get_list : type n.
    (n, kinetic) term -> (n, kinetic) term Bwd.t -> (n, kinetic) term Bwd.t option =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, []) when c = Constr.intern "nil" -> Some elts
  | Constr (c, _, [ car; cdr ]) when c = Constr.intern "cons" ->
      get_list (CubeOf.find_top cdr) (Snoc (elts, CubeOf.find_top car))
  | _ -> None

let rec get_bwd : type n.
    (n, kinetic) term -> (n, kinetic) term list -> (n, kinetic) term Bwd.t option =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, []) when c = Constr.intern "emp" -> Some (Bwd.of_list elts)
  | Constr (c, _, [ rdc; rac ]) when c = Constr.intern "snoc" ->
      get_bwd (CubeOf.find_top rdc) (CubeOf.find_top rac :: elts)
  | _ -> None

let rec synths : type n. (n, kinetic) term -> bool = function
  | Var _ | Const _
  | Meta (_, _)
  | MetaEnv (_, _)
  | Field (_, _, _)
  | UU _
  | Inst (_, _)
  | Pi (_, _, _)
  | App (_, _)
  | Act (_, _, _)
  | Let (_, _, _) -> true
  | Constr (_, _, _) | Lam (_, _) | Struct _ -> false
  | Unshift (_, _, tm) -> synths tm
  | Unact (_, tm) -> synths tm
  | Shift (_, _, tm) -> synths tm
  | Weaken tm -> synths tm

(* If the insertion on a field is (1,0,1), we omit the numeric annotation. *)
let show_ins : type nk n k. (nk, n, k) insertion -> int list =
 fun ins ->
  match (D.compare_zero (cod_left_ins ins), D.compare_zero (cod_right_ins ins)) with
  | Zero, Pos i' -> (
      let (Is_suc (ipred, _, _)) = suc_pos i' in
      match D.compare_zero ipred with
      | Zero -> []
      | Pos _ -> ints_of_ins ins)
  | _ -> ints_of_ins ins

(* Given a term, extract its head and arguments as an application spine.  If the spine contains a field projection, stop there and return only the arguments after it, noting the field name and what it is applied to (which itself be another spine). *)
let rec get_spine : type n.
    (n, kinetic) term ->
    [ `App of (n, kinetic) term * ((n, kinetic) term * [ `Implicit | `Explicit ]) Bwd.t
    | `Field of
      (n, kinetic) term * string * int list * ((n, kinetic) term * [ `Implicit | `Explicit ]) Bwd.t
    ] =
 fun tm ->
  match tm with
  | App (fn, arg) -> (
      let module M = CubeOf.Monadic (Monad.State (struct
        type t = ((n, kinetic) term * [ `Implicit | `Explicit ]) Bwd.t
      end))
      in
      (* To append the entries in a cube to a Bwd, we iterate through it with a Bwd state. *)
      let append_bwd args =
        let all_args = not (synths (CubeOf.find_top arg)) in
        snd
          (M.miterM
             {
               it =
                 (fun fa [ x ] s ->
                   match (Display.function_boundaries (), is_id_sface fa, all_args) with
                   | `Hide, None, false -> ((), s)
                   | _, None, _ -> ((), Snoc (s, (x, `Implicit)))
                   | _ -> ((), Snoc (s, (x, `Explicit))));
             }
             [ arg ] args) in
      match get_spine fn with
      | `App (head, args) -> `App (head, append_bwd args)
      | `Field (head, fld, ins, args) -> `Field (head, fld, ins, append_bwd args))
  | Field (head, fld, ins) -> `Field (head, Field.to_string fld, show_ins ins, Emp)
  (* We have to look through identity degeneracies here. *)
  | Act (body, s, _) -> (
      match is_id_deg s with
      | Some _ -> get_spine body
      | None -> `App (tm, Emp))
  | tm -> `App (tm, Emp)

(* Build a field projection "x .fld" as a parse tree, for use as the "self" pattern in unparsing codatatypes and records.  It is built in the "entire" tightness interval and packed existentially into an observation at the call site. *)
let unparse_field_app (x : string) (fld : string) (pbij : string list) :
    (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located =
  match
    ( No.Interval.contains No.Interval.entire No.plus_omega,
      No.Interval.contains No.Interval.entire No.plus_omega )
  with
  | Some left_ok, Some right_ok ->
      let fn = unparse_var x in
      let arg = unlocated (Field (fld, pbij, [])) in
      unlocated (App { fn; arg; left_ok; right_ok })
  | _ -> fatal (Anomaly "impossible interval in unparse_field_app")

(* Add the new variables bound by a match branch to the name context, using the branch's stored pattern-variable names, and returning the (possibly freshened) names in order. *)
let rec add_match_vars : type a b m ab.
    m D.t ->
    a Names.t ->
    (string option, b) Vec.t ->
    (a, b, m, ab) Tbwd.snocs ->
    ab Names.t * string list =
 fun dim vars names snocs ->
  match (names, snocs) with
  | [], Zero -> (vars, [])
  | name :: names, Suc snocs ->
      let x, vars = Names.add_cube dim vars name in
      let vars, xs = add_match_vars dim vars names snocs in
      (vars, x :: xs)

(* The result of reading back a constructor's argument telescope from a value: the telescope as a term, plus the context and environment extended by fresh variables for its arguments (needed to read back the index values that follow it), and the (top-dimensional) values of those fresh argument variables in order (needed to build the constructor-as-a-function for degenerate datatypes). *)
type (_, _, _) rb_tel =
  | Rb_tel :
      ('e, 'c, 'ec) Term.tel
      * ('lev, 'ec) Ctx.t
      * (D.zero, 'ac) Value.env
      * kinetic Value.value list
      -> ('e, 'c, 'ac) rb_tel

(* Read back a (zero-dimensional) telescope of value-level types into a term-level telescope in the readback context, introducing a fresh variable for each entry. *)
let rec readback_tel : type lev e a c ac.
    (lev, e) Ctx.t -> (D.zero, a) Value.env -> (a, c, ac) Term.tel -> (e, c, ac) rb_tel =
 fun ctx env tel ->
  match tel with
  | Emp -> Rb_tel (Emp, ctx, env, [])
  | Ext (name, rty, rest) ->
      let ety = Norm.eval_term env rty in
      let newvars, newnfs = Domvars.dom_vars ctx (CubeOf.singleton ety) in
      let trty = readback_val ~sort:`Type ctx ety in
      let ctx = Ctx.cube_vis ctx name newnfs in
      let env = Value.Ext (env, D.plus_zero D.zero, Ok newvars) in
      let (Rb_tel (resttel, fctx, fenv, restvals)) = readback_tel ctx env rest in
      Rb_tel (Ext (name, trty, resttel), fctx, fenv, CubeOf.find_top newvars :: restvals)

(* The result of reading back a value-level datatype constructor: its argument telescope and, for an indexed datatype, the output type (the datatype family applied to the constructor's index values). *)
type _ rb_constr = Rb_constr : ('e, 'c, 'ec) Term.tel * ('ec, kinetic) term option -> 'e rb_constr

(* Read back a value-level datatype constructor (at dimension zero) into the readback context: its argument telescope, and its output type if the datatype is indexed.  The output type is the datatype family (passed in, e.g. "Vec N") applied to the constructor's index values, which are obtained by evaluating its stored index terms at the fresh argument variables (as in the Constr branch of Check.check). *)
let readback_dataconstr : type lev e ij.
    (lev, e) Ctx.t -> Value.normal option -> (D.zero, ij) Value.dataconstr -> e rb_constr =
 fun ctx family (Dataconstr { env; args; indices; output = _ }) ->
  let (Rb_tel (tel, fctx, fenv, _)) = readback_tel ctx env args in
  let output =
    match (family, indices) with
    | _, [] -> None
    | None, _ -> None
    | Some family, _ ->
        let idxvals =
          Vec.to_list_map (fun ix -> CubeOf.singleton (Norm.eval_term fenv ix)) indices in
        let out = List.fold_left Norm.apply_term family.tm idxvals in
        Some (readback_val ~sort:`Type fctx out) in
  Rb_constr (tel, output)

(* Read back the (higher-dimensional) function-type of a constructor of a *degenerate* (positive substitution dimension m) datatype.  The idea is that a constructor's type is morally a function type "(args) → D ...", and the type of the degenerate constructor is the degeneration of that function.  We can't take the degeneration of a constructor directly (there's no "tyof_constr"), but we *can* form the constructor-as-a-function "λ args. c args" together with its function-type "(args) → out", and then act on it by the pure degeneracy deg_zero m using act_ty.  Acting on a function-type instantiates its codomain at the faces of the function, which here are the lower-dimensional constructors, exactly producing e.g. "List⁽ᵉ⁾ (Id A) (cons. x₀ xs₀) (cons. x₁ xs₁)".  Reading back the result gives a higher-dimensional pi-type term, which unparses (via unparse_higher_pi) as "{x₀ x₁ : A} (x₂ : Id A x₀ x₁) … →⁽ᵉ⁾ …".  The constructor's output type "out" is the stored output term (for an indexed datatype, e.g. "Vec A (suc. n)") evaluated at the fresh argument variables; if there is no stored output (a non-indexed datatype), it is the underlying zero-dimensional datatype d0 itself (one face of the degenerate one). *)
let readback_degenerate_constr : type lev e m ij.
    (lev, e) Ctx.t ->
    m D.t ->
    kinetic Value.value ->
    Constr.t ->
    (D.zero, ij) Value.dataconstr ->
    (e, kinetic) term =
 fun ctx m d0 c (Dataconstr { env; args; indices = _; output }) ->
  let (Rb_tel (tel, fctx, fenv, argvals)) = readback_tel ctx env args in
  let output_value =
    match output with
    | Some o -> Norm.eval_term fenv o
    | None -> d0 in
  let output_term = readback_val ~sort:`Type fctx output_value in
  let argvar_terms = List.map (fun v -> readback_val fctx v) argvals in
  let cbody = Term.Constr (c, D.zero, List.map CubeOf.singleton argvar_terms) in
  let cfun = Telescope.lams tel cbody in
  let cty = Telescope.pis tel output_term in
  let cfun = Norm.eval_term (Ctx.env ctx) cfun in
  let cty = Norm.eval_term (Ctx.env ctx) cty in
  let ft = Act.act_ty cfun cty (deg_zero m) in
  readback_val ~sort:`Type ctx ft

(* The primary unparsing function.  Given the variable names, unparse a term into given tightness intervals. *)
let rec unparse : type n lt ls rt rs s.
    n Names.t ->
    (n, s) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars tm li ri ->
  match tm with
  | Var x -> unlocated (Ident (Names.lookup vars x, []))
  | Const c -> (
      match Scope.Situation.unparse (`Constant c) with
      | Some { keys = _; notn = Wrap notn; pat_vars = []; val_vars = []; inner_symbols } ->
          unparse_notation notn [] inner_symbols li ri
      | _ -> unlocated (Ident (Scope.name_of c, [])))
  | Meta (v, _) ->
      unlocated (Ident ([ (if Display.metas () == `Numbered then Meta.name v else "?") ], []))
  (* NB: We don't currently print the arguments of a metavariable. *)
  | MetaEnv (v, _) ->
      unlocated
        (Ident ([ (if Display.metas () == `Numbered then Meta.name v ^ "{…}" else "?") ], []))
  | Field (tm, fld, ins) ->
      unparse_spine vars (`Field (tm, Field.to_string fld, show_ins ins)) Emp li ri
  | UU n ->
      unparse_act ~sort:(`Type, `Canonical) vars
        {
          unparse =
            (fun _ _ ->
              unlocated (outfix ~notn:universe ~inner:(Single (wstok (Ident [ "Type" ])))));
        }
        (deg_zero n) li ri
  | Inst (ty, tyargs) -> unparse_inst vars ty vars tyargs li ri
  | Pi (_, doms, _) ->
      let dim, notn =
        match D.compare_zero (CubeOf.dim doms) with
        | Zero -> (`Arrow, arrow)
        | Pos _ -> (`DblArrow, dblarrow) in
      unparse_pis dim notn vars Emp tm li ri
  | App _ -> (
      match get_spine tm with
      | `App (fn, args) ->
          unparse_spine vars (`Term fn) (Bwd.map (make_unparser_implicit vars) args) li ri
      | `Field (head, fld, ins, args) ->
          unparse_spine vars
            (`Field (head, fld, ins))
            (Bwd.map (make_unparser_implicit vars) args)
            li ri)
  | Act (tm, s, sort) ->
      unparse_act ~sort vars { unparse = (fun li ri -> unparse vars tm li ri) } s li ri
  | Let (x, tm, body) -> (
      let tm = unparse vars tm No.Interval.entire No.Interval.entire in
      (* If a let-in doesn't fit in its interval, we have to parenthesize it. *)
      let x, vars = Names.add_cube D.zero vars x in
      match No.Interval.contains ri No.minus_omega with
      | Some right_ok ->
          let body = unparse vars body No.Interval.entire ri in
          unlocated
            (prefix ~notn:letin
               ~inner:
                 (Multiple
                    (wstok Let, Emp <: Term (unparse_var x) <: mktok Coloneq <: Term tm, wstok In))
               ~last:body ~right_ok)
      | None ->
          let body = unparse vars body No.Interval.entire No.Interval.entire in
          let right_ok = No.le_refl No.minus_omega in
          parenthesize
            (unlocated
               (prefix ~notn:letin
                  ~inner:
                    (Multiple
                       (wstok Let, Emp <: Term (unparse_var x) <: mktok Coloneq <: Term tm, wstok In))
                  ~last:body ~right_ok)))
  | Lam (Variables (m, _, _), _) ->
      let cube =
        match D.compare m D.zero with
        | Eq -> `Normal
        | Neq -> `Cube in
      unparse_lam cube vars Emp tm li ri
  | Struct (type m et) ({ eta = Eta; fields; dim = _; energy = _ } : (m, n, s, et) struct_args) ->
      unlocated
        (outfix ~notn:Postprocess.parens
           ~inner:
             (Multiple
                ( wstok LParen,
                  Bwd_extra.intersperse (mktok (Op ","))
                    (Bwd.fold_left
                       (fun acc
                            (Term.StructfieldAbwd.Entry
                               (type i)
                               ((fld, structfield) : i Field.t * (i, m * n * s * et) Structfield.t))
                          ->
                         let (Lower (fldtm, lbl)) = structfield in
                         let fldtm = unparse vars fldtm No.Interval.entire No.Interval.entire in
                         Snoc
                           ( acc,
                             Term
                               (match lbl with
                               | `Labeled ->
                                   unlocated
                                     (infix ~notn:coloneq
                                        ~first:(unlocated (Ident ([ Field.to_string fld ], [])))
                                        ~inner:(Single (wstok Coloneq))
                                        ~last:fldtm ~left_ok:(No.le_refl No.minus_omega)
                                        ~right_ok:(No.le_refl No.minus_omega))
                               (* An unlabeled 1-tuple is currently unparsed as (_ := M). *)
                               | `Unlabeled when Bwd.length fields = 1 ->
                                   unlocated
                                     (infix ~notn:coloneq ~first:(unlocated (Placeholder []))
                                        ~inner:(Single (wstok Coloneq))
                                        ~last:fldtm ~left_ok:(No.le_refl No.minus_omega)
                                        ~right_ok:(No.le_refl No.minus_omega))
                               | `Unlabeled -> fldtm) ))
                       Emp fields),
                  wstok RParen )))
  | Constr (c, _, args) -> (
      (* TODO: This doesn't print the dimension.  This is correct since constructors don't have to (and in fact *can't* be) written with their dimension, but it could also be somewhat confusing, e.g. printing "refl (0:N)" yields just "0", and similarly "refl (nil. : List N)" yields "nil.". *)
      match unparse_numeral tm with
      | Some tm -> tm.unparse li ri
      | None ->
          let args = of_list_map (fun x -> make_unparser vars (CubeOf.find_top x)) args in
          unparse_spine vars (`Constr c) args li ri)
  | Realize tm -> unparse vars tm li ri
  | Canonical c -> unparse_canonical vars c li ri
  | Struct { eta = Noeta; dim; fields; energy = _ } -> unparse_comatch vars dim fields li ri
  | Match { tm; dim; branches } -> unparse_match vars tm dim branches li ri
  | Unshift _ -> fatal (Unimplemented "unparsing unshifts")
  (* An Unact only changes the dimension/action, not which variables are in scope, so for display we can simply unparse its body. *)
  | Unact (_, tm) -> unparse vars tm li ri
  | Shift _ -> fatal (Unimplemented "unparsing shifts")
  | Weaken tm -> unparse (Names.remove vars Now) tm li ri

(* The master unparsing function can easily be delayed. *)
and make_unparser : type n. n Names.t -> (n, kinetic) term -> unparser =
 fun vars tm -> { unparse = (fun li ri -> unparse vars tm li ri) }

(* A version that wraps implicit arguments in braces. *)
and make_unparser_implicit : type n.
    n Names.t -> (n, kinetic) term * [ `Implicit | `Explicit ] -> unparser =
 fun vars (tm, i) ->
  match i with
  | `Explicit -> { unparse = (fun li ri -> unparse vars tm li ri) }
  | `Implicit ->
      {
        unparse =
          (fun _ _ ->
            let tm = unparse vars tm No.Interval.entire No.Interval.entire in
            braceize tm);
      }

(* Unparse a canonical type (a datatype or codatatype/record). *)
and unparse_canonical : type n lt ls rt rs.
    n Names.t ->
    n Term.canonical ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars c li ri ->
  match c with
  | Data { indices = _; constrs; discrete = _ } -> unparse_data vars constrs li ri
  | Codata { eta; dim; fields; _ } -> unparse_codata vars eta dim fields li ri

(* Unparse a codatatype (Noeta, "codata [ x .fld : ty | ... ]") or record type (Eta, "sig ( x .fld : ty, ... )").  In both cases we use a single self-variable, and the "self record" surface syntax with explicit field projections, which handles dependence of later field types on earlier ones. *)
and unparse_codata : type n a et lt ls rt rs.
    a Names.t ->
    (potential, et) eta ->
    n D.t ->
    (a * n * et) Term.CodatafieldAbwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars eta _dim fields _li _ri ->
  let x, selfvars = Names.add_cube _dim vars None in
  let unparse_field : type i.
      observation Bwd.t ->
      (observation Bwd.t -> observation Bwd.t) ->
      i Field.t ->
      (i, a * n * et) Term.Codatafield.t ->
      observation Bwd.t =
   fun acc sep fld cf ->
    match cf with
    | Term.Codatafield.Lower tm ->
        let pat = unparse_field_app x (Field.to_string fld) [] in
        let ty = unparse selfvars tm No.Interval.entire No.Interval.entire in
        sep acc <: Term pat <: mktok Colon <: Term ty
    | Term.Codatafield.Higher _ -> fatal (Unimplemented "unparsing higher codata fields") in
  match eta with
  | Noeta ->
      let inner =
        Bwd.fold_left
          (fun acc (Term.CodatafieldAbwd.Entry (fld, cf)) ->
            unparse_field acc (fun acc -> acc <: mktok (Op "|")) fld cf)
          (Snoc (Emp, mktok LBracket))
          fields in
      unlocated (outfix ~notn:codata ~inner:(Multiple (wstok Codata, inner, wstok RBracket)))
  | Eta ->
      let inner, _ =
        Bwd.fold_left
          (fun (acc, first) (Term.CodatafieldAbwd.Entry (fld, cf)) ->
            ( unparse_field acc (fun acc -> if first then acc else acc <: mktok (Op ",")) fld cf,
              false ))
          (Snoc (Emp, mktok LParen), true)
          fields in
      unlocated (outfix ~notn:record ~inner:(Multiple (wstok Sig, inner, wstok RParen)))

(* Unparse the argument telescope of a datatype constructor as a Bwd of "(x : A)" pi-domain unparsers, returning also the name context extended by the telescope variables. *)
and unparse_tel_args : type b bc cc.
    b Names.t -> (b, cc, bc) Term.tel -> unparser Bwd.t -> bc Names.t * unparser Bwd.t =
 fun vars tel acc ->
  match tel with
  | Emp -> (vars, acc)
  | Ext (name, ty, rest) ->
      let uty = unparse vars ty (interval_right asc) No.Interval.entire in
      let x, newvars = Names.add_cube D.zero vars name in
      unparse_tel_args newvars rest (acc <: { unparse = (fun _ _ -> unparse_pi_dom x uty) })

(* Assemble the display of a constructor "constr. (x:A) ...", optionally ascribed by an output type "constr. (x:A) ... : OUT". *)
and unparse_constr_display : type lt ls rt rs.
    Constr.t ->
    unparser Bwd.t ->
    unparser option ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun c argunps output li ri ->
  let head = { unparse = (fun _ _ -> unlocated (Constr (Constr.to_string c, []))) } in
  match output with
  | None -> unparse_spine Names.empty (`Unparser head) argunps li ri
  | Some output -> (
      let first = unparse_spine Names.empty (`Unparser head) argunps li (interval_left asc) in
      let last = output.unparse (interval_right asc) ri in
      match (No.Interval.contains li No.minus_omega, No.Interval.contains ri No.minus_omega) with
      | Some left_ok, Some right_ok ->
          unlocated (infix ~notn:asc ~first ~inner:(Single (wstok Colon)) ~last ~left_ok ~right_ok)
      | _ -> fatal (Anomaly "impossible interval unparsing datatype constructor"))

(* Unparse a datatype "data [ | constr. (x:A) ... | ... ]" from a term-level datatype.  Since a term-level (anonymous) datatype doesn't know its own name, the head of a constructor's output type is displayed as a placeholder. *)
and unparse_data : type a i lt ls rt rs.
    a Names.t ->
    (Constr.t, (a, i) Term.dataconstr) Abwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars constrs _li _ri ->
  let inner =
    Bwd.fold_left
      (fun acc (c, dc) ->
        let cterm = unparse_dataconstr vars c dc No.Interval.entire No.Interval.entire in
        acc <: mktok (Op "|") <: Term cterm)
      (Snoc (Emp, mktok LBracket))
      constrs in
  unlocated (outfix ~notn:data ~inner:(Multiple (wstok Data, inner, wstok RBracket)))

and unparse_dataconstr : type a i lt ls rt rs.
    a Names.t ->
    Constr.t ->
    (a, i) Term.dataconstr ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars c (Dataconstr { args; indices; output = _ }) li ri ->
  let bcvars, argunps = unparse_tel_args vars args Emp in
  let output =
    match Vec.to_list indices with
    | [] -> None
    | idxs ->
        let idxargs =
          Bwd.of_list
            (List.map (fun idx -> { unparse = (fun li ri -> unparse bcvars idx li ri) }) idxs) in
        let ph = { unparse = (fun _ _ -> unlocated (Placeholder [])) } in
        Some { unparse = (fun li ri -> unparse_spine bcvars (`Unparser ph) idxargs li ri) } in
  unparse_constr_display c argunps output li ri

(* Unparse a value-level datatype, including each constructor's output type, computed by readback_dataconstr from the datatype family. *)
and unparse_data_value : type lev e ij lt ls rt rs.
    (lev, e) Ctx.t ->
    Value.normal option ->
    (Constr.t, (D.zero, ij) Value.dataconstr) Abwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun ctx family constrs _li _ri ->
  let names = Names.of_ctx ctx in
  let inner =
    Bwd.fold_left
      (fun acc (c, dc) ->
        let (Rb_constr (tel, output)) = readback_dataconstr ctx family dc in
        let bcvars, argunps = unparse_tel_args names tel Emp in
        let output =
          Option.map (fun out -> { unparse = (fun li ri -> unparse bcvars out li ri) }) output in
        let cterm = unparse_constr_display c argunps output No.Interval.entire No.Interval.entire in
        acc <: mktok (Op "|") <: Term cterm)
      (Snoc (Emp, mktok LBracket))
      constrs in
  unlocated (outfix ~notn:data ~inner:(Multiple (wstok Data, inner, wstok RBracket)))

(* Unparse a value-level *degenerate* (positive substitution dimension) datatype, displaying each constructor as "c. : <higher-dimensional function type>" (e.g. "cons. : {x₀ x₁ : A} (x₂ : Id A x₀ x₁) … →⁽ᵉ⁾ List⁽ᵉ⁾ (Id A) (cons. x₀ xs₀) (cons. x₁ xs₁)").  We obtain the underlying zero-dimensional datatype d0 as a face of the degenerate one (the boundary of its type, a degenerate universe), and read back each constructor's degenerate function-type with readback_degenerate_constr.  Returns None (falling back to displaying the neutral) for indexed datatypes, which aren't yet supported. *)
and unparse_degenerate_data_value : type a b lt ls rt rs.
    (a, b) Ctx.t ->
    kinetic Value.value ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located option =
 fun ctx tm _li _ri ->
  match tm with
  | Value.Neu { ty; _ } -> (
      match View.view_type (Lazy.force ty) "unparse_degenerate_data_value" with
      | Canonical (_, UU m, ins0, boundary) -> (
          let Eq = eq_of_ins_zero ins0 in
          (* The underlying zero-dimensional datatype is a vertex of the degenerate one, recovered from the boundary faces of its (degenerate-universe) type. *)
          let dom = TubeOf.plus_cube (Value.val_of_norm_tube boundary) (CubeOf.singleton tm) in
          match vertex m with
          | None -> None
          | Some v -> (
              let d0 = CubeOf.find dom v in
              match View.view_type d0 "unparse_degenerate_data_value d0" with
              | Canonical (_, Data d0_args, _, _) -> (
                  match D.compare_zero d0_args.dim with
                  | Pos _ -> None
                  | Zero ->
                      let names = Names.of_ctx ctx in
                      let inner =
                        Bwd.fold_left
                          (fun acc (c, dc) ->
                            let ft = readback_degenerate_constr ctx m d0 c dc in
                            let output = { unparse = (fun li ri -> unparse names ft li ri) } in
                            let cterm =
                              unparse_constr_display c Emp (Some output) No.Interval.entire
                                No.Interval.entire in
                            acc <: mktok (Op "|") <: Term cterm)
                          (Snoc (Emp, mktok LBracket))
                          d0_args.constrs in
                      Some
                        (unlocated
                           (outfix ~notn:data ~inner:(Multiple (wstok Data, inner, wstok RBracket)))))
              | _ -> None))
      | _ -> None)
  | _ -> None

(* "about" on a bare datatype *constant* such as Vec, whose value is a function (the parameter abstraction) eventually reaching a datatype.  We apply it to fresh parameter variables until we reach the datatype value (whose family "tyfam" is then populated), display that with unparse_data_value, and re-abstract over the parameters.  This is what lets "about Vec" show "A ↦ data [ ... : Vec A ... ]" with the real family head rather than a placeholder.  Returns None for anything that isn't a (parameterized) datatype, so the caller falls back to displaying the stored case tree.

   LIMITATION: this only descends through *parameter abstractions* (lambdas).  If a datatype appears nested inside a match or comatch/tuple in the case tree (e.g. "def Vec (n:N) : Type → Type ≔ match n [ zero. ↦ data [ ... : Vec n A ] | suc. m ↦ data [ ... : Vec (suc. m) A ] ]"), we hit a stuck (Unrealized) neutral here and fall back to unparsing the stored case tree, where the nested datatype is anonymous and its constructors' output-type heads are shown as a placeholder "_".  Recovering those heads would require re-deriving the case tree by splitting each match and evaluating its branches (the only way to repopulate "tyfam" per branch); since it's a rare shape, we don't do it. *)
and unparse_constant_value : type a b. (a, b) Ctx.t -> kinetic Value.value -> unparser option =
 fun ctx value ->
  match value with
  | Value.Neu { value = v; ty; _ } -> (
      match Norm.force_eval v with
      | Val (Value.Canonical { canonical = Value.Data data_args; ins; _ }) -> (
          match (is_id_ins ins, D.compare_zero data_args.dim) with
          | Some _, Zero ->
              let family = Option.map Lazy.force !(data_args.tyfam) in
              Some
                { unparse = (fun li ri -> unparse_data_value ctx family data_args.constrs li ri) }
          | _ -> None)
      | Val (Value.Lam (xs, _)) -> (
          (* A function: apply it to a fresh parameter variable and recurse, then re-abstract.  We take the parameter's name from the lambda-abstraction (the definition), not the function-type (whose binder may be anonymous). *)
          match View.view_type (Lazy.force ty) "unparse_constant_value" with
          | Canonical (_, Pi (_, doms, _), pins, _) -> (
              let Eq = eq_of_ins_zero pins in
              match D.compare_zero (CubeOf.dim doms) with
              | Zero -> (
                  let pname, _ = Names.add_cube D.zero (Names.of_ctx ctx) (top_variable xs) in
                  let argvar, argnf = Domvars.dom_vars ctx doms in
                  let ctx = Ctx.cube_vis ctx (Some pname) argnf in
                  let value = Norm.apply_term value argvar in
                  match unparse_constant_value ctx value with
                  | None -> None
                  | Some body ->
                      Some
                        {
                          unparse =
                            (fun (type lt ls rt rs)
                              (li : (lt, ls) No.iinterval)
                              (ri : (rt, rs) No.iinterval)
                            ->
                              match
                                ( No.Interval.contains li No.minus_omega,
                                  No.Interval.contains ri No.minus_omega )
                              with
                              | Some left_ok, Some right_ok ->
                                  let li_ok =
                                    No.lt_trans Any_strict left_ok No.minusomega_lt_plusomega in
                                  let first =
                                    unparse_abs
                                      (Snoc (Emp, (pname, `Explicit)))
                                      li li_ok No.minusomega_lt_plusomega in
                                  let last = body.unparse No.Interval.entire ri in
                                  unlocated
                                    (infix ~notn:abs ~first
                                       ~inner:(Single (wstok Mapsto))
                                       ~last ~left_ok ~right_ok)
                              | _ ->
                                  let first =
                                    unparse_abs
                                      (Snoc (Emp, (pname, `Explicit)))
                                      No.Interval.entire (No.le_plusomega No.minus_omega)
                                      No.minusomega_lt_plusomega in
                                  let last = body.unparse No.Interval.entire No.Interval.entire in
                                  let left_ok = No.le_refl No.minus_omega in
                                  let right_ok = No.le_refl No.minus_omega in
                                  parenthesize
                                    (unlocated
                                       (infix ~notn:abs ~first
                                          ~inner:(Single (wstok Mapsto))
                                          ~last ~left_ok ~right_ok)));
                        })
              | Pos _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

(* Unparse a match "match tm [ | constr. x ... |-> body | ... ]".  Refuted branches are omitted; an all-refuted (or empty) match prints as "match tm [ ]". *)
and unparse_match : type n m lt ls rt rs.
    n Names.t ->
    (n, kinetic) term ->
    m D.t ->
    (n, m) Term.branch Constr.Map.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars tm dim branches _li _ri ->
  let mapsto =
    match D.compare_zero dim with
    | Zero -> Token.Mapsto
    | Pos _ -> Token.DblMapsto in
  let disc = unparse vars tm No.Interval.entire No.Interval.entire in
  let inner =
    Constr.Map.fold
      (fun c br acc ->
        match br with
        | Term.Refute -> acc
        | Term.Branch (names, snocs, perm, body) ->
            let newvars, xs = add_match_vars dim vars names snocs in
            let bodyvars = Names.permute perm newvars in
            let args =
              Bwd.of_list (List.map (fun x -> { unparse = (fun _ _ -> unparse_var x) }) xs) in
            let pat = unparse_spine vars (`Constr c) args No.Interval.entire No.Interval.entire in
            let ubody = unparse bodyvars body No.Interval.entire No.Interval.entire in
            acc <: mktok (Op "|") <: Term pat <: mktok mapsto <: Term ubody)
      branches
      (Snoc (Emp, Term disc) <: mktok LBracket) in
  unlocated (outfix ~notn:implicit_mtch ~inner:(Multiple (wstok Match, inner, wstok RBracket)))

(* Unparse a comatch "[ .fld |-> body | ... ]".  An empty comatch prints with the empty (co)match notation. *)
and unparse_comatch : type n a s et lt ls rt rs.
    a Names.t ->
    n D.t ->
    (n * a * s * et) Term.StructfieldAbwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars _dim fields _li _ri ->
  match fields with
  | Emp ->
      unlocated
        (outfix ~notn:empty_co_match ~inner:(Multiple (wstok LBracket, Emp, wstok RBracket)))
  | _ ->
      let inner =
        Bwd.fold_left
          (fun acc
               (Term.StructfieldAbwd.Entry
                  (type i)
                  ((fld, sf) : i Field.t * (i, n * a * s * et) Term.Structfield.t)) ->
            match sf with
            | Term.Structfield.Lower (tm, _) ->
                let pat = unlocated (Field (Field.to_string fld, [], [])) in
                let ubody = unparse vars tm No.Interval.entire No.Interval.entire in
                acc <: mktok (Op "|") <: Term pat <: mktok Mapsto <: Term ubody
            | Term.Structfield.Higher _ | Term.Structfield.LazyHigher _ ->
                fatal (Unimplemented "unparsing higher comatch fields"))
          Emp fields in
      unlocated (outfix ~notn:comatch ~inner:(Multiple (wstok LBracket, inner, wstok RBracket)))

(* If a (normalized) value is a neutral whose potential value is a canonical type (a datatype, codatatype, or record), read it back and unparse it as the corresponding canonical-type declaration.  This lets us display, for instance, "List Nat" as "data [ nil. | cons. (x : Nat) (xs : List Nat) ]".  Returns None if the value is not such a neutral, or if it is higher-dimensional (in which case the caller falls back to other display methods). *)
and unparse_canonical_value : type a b lt ls rt rs.
    (a, b) Ctx.t ->
    kinetic Value.value ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located option =
 fun ctx tm li ri ->
  match tm with
  | Value.Neu { value; _ } -> (
      match Norm.force_eval value with
      | Val (Value.Canonical { canonical; ins; _ }) -> (
          match canonical with
          | Value.Data data_args -> (
              match (is_id_ins ins, D.compare_zero data_args.dim) with
              | Some _, Zero ->
                  let family = Option.map Lazy.force !(data_args.tyfam) in
                  Some (unparse_data_value ctx family data_args.constrs li ri)
              (* A degenerate (positive substitution dimension) datatype is displayed by reconstructing each constructor's higher-dimensional function-type; see readback_degenerate_constr.  Currently only non-indexed degenerate datatypes are supported; indexed ones fall back to displaying the neutral. *)
              | Some _, Pos _ -> unparse_degenerate_data_value ctx tm li ri
              | None, _ -> None)
          (* Codatatypes/records are handled uniformly whether 0-dimensional, intrinsically higher (Gel-like), or degenerate: we introduce a self variable of the codatatype's full dimension and read back each field's type with tyof_field. *)
          | Value.Codata codata_args -> unparse_codata_value ctx tm codata_args li ri
          | Value.UU _ | Value.Pi _ -> None)
      | _ -> None)
  | _ -> None

(* Unparse a value-level codatatype/record by introducing a self variable of its full dimension (via dom_vars, which gives the top self-variable the fully-instantiated codatatype as its type) and reading back the type of each field with tyof_field.  This handles 0-dimensional, intrinsically-higher (Gel-like), and degenerate codatatypes uniformly, displaying the in-practice (possibly higher-dimensional) field types. *)
and unparse_codata_value : type a b cm cn cc ca cet lt ls rt rs.
    (a, b) Ctx.t ->
    kinetic Value.value ->
    (cm, cn, cc, ca, cet) Value.codata_args ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located option =
 fun ctx tm codata_args _li _ri ->
  let eta = codata_args.eta in
  let evaldim = Value.dim_env codata_args.env in
  match tm with
  | Value.Neu { ty; _ } -> (
      match View.view_type (Lazy.force ty) "unparse_codata_value" with
      | Canonical (_, UU mk, ins0, boundary) ->
          (* The universe has intrinsic dimension zero, so its substitution dimension equals its total dimension mk. *)
          let Eq = eq_of_ins_zero ins0 in
          (* The self variable ranges over the codatatype; dom_vars builds its boundary faces and gives the top face the fully-instantiated codatatype as its type. *)
          let dom = TubeOf.plus_cube (Value.val_of_norm_tube boundary) (CubeOf.singleton tm) in
          let selfvars, selfnfs = Domvars.dom_vars ctx dom in
          let self_top = CubeOf.find_top selfvars in
          let self_top_ty = (Ctx.Binding.value (CubeOf.find_top selfnfs)).ty in
          (* Pick a name for the self variable, and add it to the readback context so we can read back the field types referring to it. *)
          let selfname, _ = Names.add_cube mk (Names.of_ctx ctx) None in
          let ctx = Ctx.cube_vis ctx (Some selfname) selfnfs in
          (* Read back and unparse the type of one field instance, in the given (possibly degenerated) display context. *)
          let display_instance : type da db i.
              (da, db) Ctx.t ->
              i Field.t ->
              string list ->
              kinetic Value.value ->
              (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located
              * (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located =
           fun dctx fld pbij ety ->
            ( unparse_field_app selfname (Field.to_string fld) pbij,
              unparse (Names.of_ctx dctx)
                (readback_val ~sort:`Type dctx ety)
                No.Interval.entire No.Interval.entire ) in
          (* Collect every field instance, i.e. every field that must be given when comatching against this codatatype.  Lower fields have exactly one instance; a higher field of intrinsic dimension i has one instance for each partial bijection between the codatatype's evaluation dimension and i.  Projectable instances (zero remaining) are read back in the self-variable context; non-projectable ones (the declaration form .e and intermediate forms .e1) are read back in a context degenerated by the remaining dimensions. *)
          let instances =
            Bwd.fold_left
              (fun acc
                   (Term.CodatafieldAbwd.Entry
                      (type i)
                      ((fld, cf) : i Field.t * (i, ca * cn * cet) Term.Codatafield.t)) ->
                match cf with
                | Term.Codatafield.Lower _ ->
                    let ety =
                      Norm.tyof_field (Ok self_top) self_top_ty fld ~shuf:Norm.Trivial
                        (ins_zero evaldim) in
                    acc <: display_instance ctx fld [] ety
                | Term.Codatafield.Higher (_, _) ->
                    Seq.fold_left
                      (fun acc (Pbij_between (pbij : (cm, i, _) pbij)) ->
                        let (Pbij (fldins, fldshuf)) = pbij in
                        match D.compare_zero (left_shuffle fldshuf) with
                        | Zero ->
                            let Eq = eq_of_zero_shuffle fldshuf in
                            let ety =
                              Norm.tyof_field (Ok self_top) self_top_ty fld ~shuf:Norm.Trivial
                                fldins in
                            acc <: display_instance ctx fld (strings_of_pbij pbij) ety
                        | Pos _ ->
                            (* Non-projectable instance: degenerate the context by the remaining dimensions, and build the nontrivial shuffleable to compute the field type there. *)
                            let r = left_shuffle fldshuf in
                            let (Degctx.Degctx (_, dctx, denv)) = Degctx.degctx ctx r in
                            let termctx =
                              Lazy.force codata_args.termctx
                              <|> Anomaly "missing termctx for higher codata field" in
                            let shuf =
                              higher_codatafield_shuffleable ctx
                                (Value.length_env codata_args.env)
                                termctx denv r fldshuf in
                            let ety = Norm.tyof_field (Ok self_top) self_top_ty fld ~shuf fldins in
                            acc <: display_instance dctx fld (strings_of_pbij pbij) ety)
                      acc
                      (all_pbij_between evaldim (Field.dim fld)))
              Emp codata_args.fields in
          (* Assemble the codata or record notation. *)
          let result =
            match eta with
            | Noeta ->
                let inner =
                  Bwd.fold_left
                    (fun acc (pat, ty) ->
                      acc <: mktok (Op "|") <: Term pat <: mktok Colon <: Term ty)
                    (Snoc (Emp, mktok LBracket))
                    instances in
                unlocated
                  (outfix ~notn:codata ~inner:(Multiple (wstok Codata, inner, wstok RBracket)))
            | Eta ->
                let inner, _ =
                  Bwd.fold_left
                    (fun (acc, first) (pat, ty) ->
                      ( (if first then acc else acc <: mktok (Op ","))
                        <: Term pat
                        <: mktok Colon
                        <: Term ty,
                        false ))
                    (Snoc (Emp, mktok LParen), true)
                    instances in
                unlocated (outfix ~notn:record ~inner:(Multiple (wstok Sig, inner, wstok RParen)))
          in
          Some result
      | _ -> None)
  | _ -> None

(* Unparse a spine with its arguments whose head could be many things: an as-yet-not-unparsed term, a constructor, a field projection, a degeneracy, or a general delayed unparsing. *)
and unparse_spine : type n lt ls rt rs.
    n Names.t ->
    [ `Term of (n, kinetic) term
    | `Constr of Constr.t
    | `Field of (n, kinetic) term * string * int list
    | `Degen of string
    | `Unparser of unparser ] ->
    unparser Bwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars head args li ri ->
  (* First we check whether the head is a term with an associated notation, and if so whether it is applied to enough arguments to instantiate that notation. *)
  match get_notation head args with
  (* If it's applied to exactly the right number of arguments, we unparse it as that notation. *)
  | Some (Wrap notn, args, inner_symbols, Emp) -> unparse_notation notn args inner_symbols li ri
  (* Otherwise, the unparsed notation has to be applied to the rest of the arguments as a spine. *)
  | Some (Wrap notn, args, inner_symbols, (Snoc _ as rest)) ->
      unparse_spine vars
        (`Unparser { unparse = (fun li ri -> unparse_notation notn args inner_symbols li ri) })
        rest li ri
  (* If not, we proceed to unparse it as an application spine, recursively. *)
  | None -> (
      match args with
      | Emp -> (
          match head with
          | `Term tm -> unparse vars tm li ri
          | `Constr c -> unlocated (Constr (Constr.to_string c, []))
          | `Field (tm, fld, ins) -> unparse_field vars tm fld ins li ri
          | `Degen s -> unlocated (Ident ([ s ], []))
          | `Unparser tm -> tm.unparse li ri)
      | Snoc (args, arg) -> (
          (* As before, if the application doesn't fit in its tightness interval, we have to parenthesize it. *)
          match (No.Interval.contains li No.plus_omega, No.Interval.contains ri No.plus_omega) with
          | Some left_ok, Some right_ok ->
              let fn = unparse_spine vars head args li No.Interval.plus_omega_only in
              let arg = arg.unparse No.Interval.empty ri in
              (* We parenthesize the argument if the style dictates and it doesn't already have parentheses. *)
              let arg =
                match Display.argstyle () with
                | `Spaces -> arg
                | `Parens -> parenthesize_maybe arg in
              unlocated (App { fn; arg; left_ok; right_ok })
          | _ ->
              let fn =
                unparse_spine vars head args No.Interval.plus_omega_only No.Interval.plus_omega_only
              in
              let arg = arg.unparse No.Interval.empty No.Interval.plus_omega_only in
              let arg =
                match Display.argstyle () with
                | `Spaces -> arg
                | `Parens -> parenthesize_maybe arg in
              let left_ok = No.le_refl No.plus_omega in
              let right_ok = No.le_refl No.plus_omega in
              parenthesize (unlocated (App { fn; arg; left_ok; right_ok }))))

and unparse_field : type n lt ls rt rs.
    n Names.t ->
    (n, kinetic) term ->
    string ->
    int list ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars tm fld ins li ri ->
  match unparse_field_var vars tm fld with
  | Some res -> res
  | None -> (
      match (No.Interval.contains li No.plus_omega, No.Interval.contains ri No.plus_omega) with
      | Some left_ok, Some right_ok ->
          let fn = unparse vars tm li No.Interval.plus_omega_only in
          let arg = unlocated (Field (fld, List.map string_of_int ins, [])) in
          unlocated (App { fn; arg; left_ok; right_ok })
      | _ ->
          let fn = unparse vars tm No.Interval.plus_omega_only No.Interval.plus_omega_only in
          let arg = unlocated (Field (fld, List.map string_of_int ins, [])) in
          let left_ok = No.le_refl No.plus_omega in
          let right_ok = No.le_refl No.plus_omega in
          parenthesize (unlocated (App { fn; arg; left_ok; right_ok })))

and unparse_field_var : type n lt ls rt rs.
    n Names.t -> (n, kinetic) term -> string -> (lt, ls, rt, rs) parse located option =
 fun vars tm fld ->
  match tm with
  | Var x -> (
      match Names.lookup_field vars x fld with
      (* If the field got used up by the lookup, we just return the variable. *)
      | Some name -> Some (unlocated (Ident (name, [])))
      (* If the field is still leftover after the lookup, we unparse it as a field. *)
      | None -> None)
  | Act (tm, deg, _) -> (
      match is_id_deg deg with
      | Some _ -> unparse_field_var vars tm fld
      | None -> None)
  | _ -> None

(* For unparsing an iterated abstraction, we group together the fully-normal variables and at-least-partially-cube variables, since they have different notations.  There is no notation for partially-cube variables, so we make them fully cube.  We recursively descend through the structure of the term, storing in 'cube' which kind of variable we are picking up and continuing until we find either a non-abstraction or an abstraction of the wrong type.  *)
and unparse_lam : type n lt ls rt rs s.
    [ `Cube | `Normal ] ->
    n Names.t ->
    (string * [ `Explicit | `Implicit ]) Bwd.t ->
    (n, s) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun cube vars xs body li ri ->
  match body with
  | Lam ((Variables (m, _, _) as boundvars), inner) -> (
      match (cube, D.compare m D.zero) with
      | `Normal, Eq | `Cube, Neq ->
          let Variables (_, _, x), vars = Names.add vars boundvars in
          let module Fold = NICubeOf.Traverse (struct
            type 'acc t = (string * [ `Explicit | `Implicit ]) Bwd.t
          end) in
          (* Apparently we need to define the folding function explicitly with a type to make it come out sufficiently polymorphic. *)
          let folder : type left k m.
              (k, m) sface ->
              (string * [ `Explicit | `Implicit ]) Bwd.t ->
              (left, k, string) NFamOf.t ->
              (left, k, unit) NFamOf.t * (string * [ `Explicit | `Implicit ]) Bwd.t =
           fun s acc (NFamOf x) ->
            let implicit =
              match is_id_sface s with
              | None -> `Implicit
              | Some _ -> `Explicit in
            (NFamOf (), Snoc (acc, (x, implicit))) in
          unparse_lam cube vars
            (snd (Fold.fold_map_left { foldmap = (fun s acc x -> folder s acc x) } xs x))
            inner li ri
      | _ -> unparse_lam_done cube vars xs body li ri)
  | _ -> unparse_lam_done cube vars xs body li ri

(* Once we hit either a non-abstraction or a different kind of abstraction, we pick the appropriate notation to use for the abstraction, depending on the kind of variables.  Note that both are (un)parsed as binary operators whose left-hand argument is an "application spine" of variables, produced here by unparse_abs. *)
and unparse_lam_done : type n lt ls rt rs s.
    [ `Cube | `Normal ] ->
    n Names.t ->
    (string * [ `Explicit | `Implicit ]) Bwd.t ->
    (n, s) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun cube vars xs body li ri ->
  let notn, mapsto =
    match cube with
    | `Cube -> (cubeabs, Token.DblMapsto)
    | `Normal -> (abs, Mapsto) in
  (* Of course, if we don't fit in the tightness interval, we have to parenthesize. *)
  match (No.Interval.contains li No.minus_omega, No.Interval.contains ri No.minus_omega) with
  | Some left_ok, Some right_ok ->
      let li_ok = No.lt_trans Any_strict left_ok No.minusomega_lt_plusomega in
      let first = unparse_abs xs li li_ok No.minusomega_lt_plusomega in
      let last = unparse vars body No.Interval.entire ri in
      unlocated (infix ~notn ~first ~inner:(Single (wstok mapsto)) ~last ~left_ok ~right_ok)
  | _ ->
      let first =
        unparse_abs xs No.Interval.entire (No.le_plusomega No.minus_omega)
          No.minusomega_lt_plusomega in
      let last = unparse vars body No.Interval.entire No.Interval.entire in
      let left_ok = No.le_refl No.minus_omega in
      let right_ok = No.le_refl No.minus_omega in
      parenthesize
        (unlocated (infix ~notn ~first ~inner:(Single (wstok mapsto)) ~last ~left_ok ~right_ok))

(* If a term is a natural number numeral (a bunch of 'suc' constructors applied to a 'zero' constructor), unparse it as that numeral; otherwise return None. *)
and unparse_numeral : type n. (n, kinetic) term -> unparser option =
 fun tm ->
  (* As in parsing, it would be better not to hardcode these constructor names. *)
  let zero = Constr.intern "zero" in
  let one = Constr.intern "one" in
  let suc = Constr.intern "suc" in
  let make_numeral dim k =
    let tm = { unparse = (fun _ _ -> unlocated (Ident ([ string_of_int k ], []))) } in
    Some
      {
        unparse =
          (fun li ri -> unparse_act ~sort:(`Other, `Other) Names.empty tm (deg_zero dim) li ri);
      } in
  let rec getsucs tm k =
    match tm with
    | Term.Constr (c, dim, []) when c = zero -> make_numeral dim k
    | Term.Constr (c, dim, []) when c = one -> make_numeral dim (k + 1)
    | Constr (c, _, [ arg ]) when c = suc -> getsucs (CubeOf.find_top arg) (k + 1)
    | _ -> None in
  getsucs tm 0

and unparse_act : type n lt ls rt rs a b.
    sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    n Names.t ->
    unparser ->
    (a, b) deg ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun ~sort vars tm s li ri ->
  match is_id_deg s with
  | Some _ -> tm.unparse li ri
  | None -> (
      match name_of_deg ~sort s with
      | Some str -> unparse_spine vars (`Degen str) (Snoc (Emp, tm)) li ri
      | None ->
          unlocated
            (Superscript (Some (tm.unparse li No.Interval.empty), unlocated (string_of_deg s), [])))

(* We unparse instantiations like application spines, since that is how they are represented in user syntax.
   TODO: How can we allow special notations for some instantiations, like x=y for Id A x y? *)
and unparse_inst : type n n' lt ls rt rs m k mk.
    (* We allow the type and its instantiation arguments to be in different contexts, for use in unparse_higher_pi. *)
    n Names.t ->
    (n, kinetic) term ->
    n' Names.t ->
    (m, k, mk, (n', kinetic) term) TubeOf.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars ty argvars tyargs li ri ->
  match (D.compare_zero (TubeOf.uninst tyargs), D.compare_zero (TubeOf.inst tyargs), ty) with
  (* A fully instantiated higher pi-type we can unparse prettily. *)
  | Zero, Pos _, Pi (x, doms, cods) -> (
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Eq ->
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (TubeOf.inst tyargs)) in
          let tyargs = TubeOf.mmap { map = (fun _ [ x ] -> Names.Named (argvars, x)) } [ tyargs ] in
          unparse_higher_pi vars Emp x doms cods tyargs li ri
      | Neq ->
          fatal (Dimension_mismatch ("unparsing higher pi", TubeOf.inst tyargs, CubeOf.dim doms)))
  | _ ->
      let tyargs = TubeOf.mmap { map = (fun _ [ x ] -> Names.Named (argvars, x)) } [ tyargs ] in
      unparse_named_inst vars ty tyargs li ri

and unparse_named_inst : type n lt ls rt rs m k mk.
    n Names.t ->
    (n, kinetic) term ->
    (m, k, mk, Names.named_term) TubeOf.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars ty tyargs li ri ->
  let module M = TubeOf.Monadic (Monad.State (struct
    type t = unparser Bwd.t
  end))
  in
  (* To append the entries in a tube to a Bwd, we iterate through it with a Bwd state. *)
  let (), args =
    M.miterM
      {
        it =
          (fun fa [ Names.Named (xvars, x) ] s ->
            (* We include the argument explicitly if it is codimension-1. *)
            match is_codim1 fa with
            | Some () -> ((), Snoc (s, make_unparser_implicit xvars (x, `Explicit)))
            | None -> (
                (* We include it implicitly if display of type boundaries is on. *)
                match Display.type_boundaries () with
                | `Show -> ((), Snoc (s, make_unparser_implicit xvars (x, `Implicit)))
                | `Hide ->
                    (* We also include it implicitly if its codimension-1 envelope is non-synthesizing *)
                    let (Tface_of fa1) = codim1_envelope fa in
                    let (Named (_, x1)) = TubeOf.find tyargs fa1 in
                    if synths x1 then ((), s)
                    else ((), Snoc (s, make_unparser_implicit xvars (x, `Implicit)))));
      }
      ~ifzero:(fun acc ->
        ( (),
          Snoc
            ( acc,
              { unparse = (fun li ri -> unparse_notation Postprocess.dot [] (`Single Dot) li ri) }
            ) ))
      [ tyargs ] Emp in
  unparse_spine vars (`Term ty) args li ri

(* We group together all the 0-dimensional or non-instantiated higher dependent pi-types in a notation, so we recursively descend through the term picking those up until we find a non-pi-type, a higher-dimensional pi-type, or a non-dependent pi-type, in which case we pass it off to unparse_pis_final. *)
and unparse_pis : type n lt ls rt rs.
    [ `Arrow | `DblArrow ] ->
    (No.strict opn, No.zero, No.nonstrict opn) notation ->
    n Names.t ->
    unparser Bwd.t ->
    (n, kinetic) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun dim notn vars accum tm li ri ->
  match tm with
  | Pi (x, doms, cods) -> (
      match (D.compare_zero (CubeOf.dim doms), dim) with
      | Zero, `Arrow | Pos _, `DblArrow -> (
          match top_variable x with
          | Some x ->
              (* dependent pi-type *)
              let Variables (_, _, x), newvars =
                Names.add vars (singleton_variables (CubeOf.dim doms) (Some x)) in
              unparse_pis dim notn newvars
                (Snoc
                   ( accum,
                     {
                       unparse =
                         (fun _ _ ->
                           unparse_pi_dom (NICubeOf.find_top x)
                             (unparse vars (CubeOf.find_top doms) (interval_right asc)
                                No.Interval.entire));
                     } ))
                (CodCube.find_top cods) li ri
          | None ->
              (* non-dependent pi-type *)
              let _, newvars = Names.add vars (singleton_variables (CubeOf.dim doms) None) in
              let dim =
                match dim with
                | `Arrow -> `Arrow None
                | `DblArrow -> `DblArrow in
              unparse_pis_final dim notn vars accum
                {
                  unparse =
                    (fun li ri ->
                      unparse_arrow dim notn
                        (make_unparser vars (CubeOf.find_top doms))
                        (make_unparser newvars (CodCube.find_top cods))
                        li ri);
                }
                li ri)
      | _ ->
          let dim =
            match dim with
            | `Arrow -> `Arrow None
            | `DblArrow -> `DblArrow in
          unparse_pis_final dim notn vars accum (make_unparser vars tm) li ri)
  | _ ->
      let dim =
        match dim with
        | `Arrow -> `Arrow None
        | `DblArrow -> `DblArrow in
      unparse_pis_final dim notn vars accum (make_unparser vars tm) li ri

(* The arrow in both dependent and non-dependent pi-types is (un)parsed as a binary operator.  In the dependent case, its left-hand argument looks like an "application spine" of ascribed variables.  Of course, it may have to be parenthesized. *)
and unparse_arrow : type lt ls rt rs m.
    [ `Arrow of m D.t option | `DblArrow ] ->
    (No.strict opn, No.zero, No.nonstrict opn) notation ->
    unparser ->
    unparser ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun dim notn dom cod li ri ->
  let tok =
    match dim with
    | `Arrow None -> sstok Arrow ""
    | `Arrow (Some dim) -> sstok Arrow (string_of_dim dim)
    | `DblArrow -> wstok DblArrow in
  match (No.Interval.contains li No.zero, No.Interval.contains ri No.zero) with
  | Some left_ok, Some right_ok ->
      let first = dom.unparse li (interval_left notn) in
      let last = cod.unparse (interval_right notn) ri in
      unlocated (infix ~notn ~first ~inner:(Single tok) ~last ~left_ok ~right_ok)
  | _ ->
      let first = dom.unparse No.Interval.entire (interval_left notn) in
      let last = cod.unparse (interval_right notn) No.Interval.entire in
      let left_ok = No.minusomega_lt_zero in
      let right_ok = No.minusomega_lt_zero in
      parenthesize (unlocated (infix ~notn ~first ~inner:(Single tok) ~last ~left_ok ~right_ok))

and unparse_pis_final : type n lt ls rt rs m.
    [ `Arrow of m D.t option | `DblArrow ] ->
    (No.strict opn, No.zero, No.nonstrict opn) notation ->
    n Names.t ->
    unparser Bwd.t ->
    unparser ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun dim notn vars accum tm li ri ->
  match split_first accum with
  | None -> tm.unparse li ri
  | Some (dom0, accum) ->
      unparse_arrow dim notn
        { unparse = (fun li ri -> unparse_spine vars (`Unparser dom0) accum li ri) }
        tm li ri

(* Unparse a single domain of a dependent pi-type. *)
and unparse_pi_dom : type lt ls rt rs.
    ?implicit:bool ->
    string ->
    (No.minus_omega, No.strict, No.minus_omega, No.nonstrict) parse located ->
    (lt, ls, rt, rs) parse located =
 fun ?(implicit = false) x dom ->
  (if implicit then braceize else parenthesize)
    (unlocated
       (infix ~notn:asc
          ~first:(unlocated (Ident ([ x ], [])))
          ~inner:(Single (wstok Colon))
          ~last:dom ~left_ok:(No.le_refl No.minus_omega) ~right_ok:(No.le_refl No.minus_omega)))

and unparse_higher_pi : type a lt ls rt rs n.
    a Names.t ->
    unparser Bwd.t ->
    n variables ->
    (n, (a, kinetic) term) CubeOf.t ->
    (n, a) CodCube.t ->
    (D.zero, n, n, Names.named_term) TubeOf.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars accum xs doms cods tyargs li ri ->
  let n = CubeOf.dim doms in
  (* Make all the variables ordinary ones by suffixing them with face names *without* a separating ".", and making sure that they all have some name. *)
  let xs, newvars = Names.add_full vars xs in
  (* Unparse each domain, instantiate it at the appropriate variables corresponding to its faces, and parenthesize or brace it to become a pi-type domain, adding them all to the accumulated list of domains. *)
  let module S = Monad.State (struct
    type t = unparser Bwd.t
  end) in
  let module MOf = CubeOf.Monadic (S) in
  let (), accum =
    MOf.miterM
      {
        it =
          (fun s [ dom ] accum ->
            let k = dom_sface s in
            let x = find_variable s xs in
            let xargs =
              TubeOf.build D.zero (D.zero_plus k)
                { build = (fun fa -> Var (Index (Now, comp_sface s (sface_of_tface fa)))) } in
            let implicit = Option.is_none (is_id_sface s) in
            (* Here we use the flexibility to have the type and the instantiation arguments in different contexts, since the type is not in the context extended by the new variables.  However, it's important that we get the context for the type by *removing* those new variables from newvars, rather than using the original vars, since that retains the extra information stored in a Names.t about how many copies of a variable there have been, for future renaming use.  *)
            let dom =
              unparse_inst (Names.remove newvars Now) dom newvars xargs (interval_right asc)
                No.Interval.entire in
            ((), Snoc (accum, { unparse = (fun _ _ -> unparse_pi_dom ~implicit x dom) })));
      }
      [ doms ] accum in
  (* The instantiation arguments 'tyargs' should already all be eta-expanded, since readback eta-expands the instantiation arguments of higher pi-types.  So we can descend into those abstractions and add the appropriate variables on which they depend to their unparsing contexts. *)
  let tyargs =
    let map : type k. (k, D.zero, n, n) tface -> Names.named_term -> Names.named_term =
     fun s (Names.Named (lamvars, lam)) ->
      let k = dom_tface s in
      let lam_xs = sub_variables (sface_of_tface s) xs in
      let _, lamvars = Names.add_strings lamvars lam_xs in
      match lam with
      | Lam (ys, body) -> (
          match D.compare (dim_variables ys) k with
          | Eq -> Named (lamvars, body)
          | Neq -> fatal (Dimension_mismatch ("unparse_higher_pi lam", dim_variables ys, k)))
      | nonlam ->
          (* This case happens when we are recursively working with the domains of another higher pi-type. *)
          let lamargs = CubeOf.build k { build = (fun s -> Var (Index (Now, s))) } in
          Named (lamvars, App (Weaken nonlam, lamargs)) in
    TubeOf.mmap { map = (fun s [ lam ] -> map s lam) } [ tyargs ] in
  (* We only need the top codomain. *)
  match CodCube.find_top cods with
  | Pi (newxs, newdoms, newcods) -> (
      (* If it's another pi-type, it must be of the same dimension since it is an (uninstantiated!) n-dimensional type, and we continue recursively. *)
      match D.compare (CubeOf.dim newdoms) n with
      | Eq -> unparse_higher_pi newvars accum newxs newdoms newcods tyargs li ri
      | Neq -> fatal (Dimension_mismatch ("unparse_higher_pi recursion", CubeOf.dim newdoms, n)))
  (* It might also be a *partially* instantiated *higher* dimensional pi-type, in which case we combine the instantiation arguments to make it fully instantiated.  We don't continue accumulating domains as in the previous case, though, because in this case the codomain has different dimension, and hence needs its own arrow. *)
  | Inst (Pi (newxs, newdoms, newcods), newtyargs) -> (
      match
        ( D.compare (TubeOf.out newtyargs) (CubeOf.dim newdoms),
          D.compare (TubeOf.uninst newtyargs) (TubeOf.inst tyargs) )
      with
      | Eq, Eq ->
          let newtyargs =
            TubeOf.mmap { map = (fun _ [ x ] -> Names.Named (newvars, x)) } [ newtyargs ] in
          let plustyargs = TubeOf.plus_tube (TubeOf.plus newtyargs) newtyargs tyargs in
          let tm =
            {
              unparse =
                (fun li ri -> unparse_higher_pi newvars Emp newxs newdoms newcods plustyargs li ri);
            } in
          unparse_pis_final (`Arrow (Some (CodCube.dim cods))) arrow vars accum tm li ri
      | Neq, _ ->
          fatal
            (Dimension_mismatch
               ("nested unparse higher pi", TubeOf.out newtyargs, CubeOf.dim newdoms))
      | _, Neq ->
          fatal
            (Dimension_mismatch
               ("nested unparse higher pi", TubeOf.uninst newtyargs, TubeOf.inst tyargs)))
  | cod ->
      (* When it's time to finish, we unparse the eventual codomain and instantiate it at the unparsed bodies of all the lambda tyargs. *)
      let tm = { unparse = (fun li ri -> unparse_named_inst newvars cod tyargs li ri) } in
      unparse_pis_final (`Arrow (Some (CodCube.dim cods))) arrow vars accum tm li ri

(* Unparse a term context, given a vector of variable names obtained by pre-uniquifying a variable list, and a list of names for the empty context that nevertheless remembers the variables in that vector, as produced by Names.uniquify_vars.  Yields not only the list of unparsed terms/types, but a corresponding list of names that can be used to unparse further objects in that context. *)
let rec unparse_ctx : type a b.
    emp Names.t ->
    [ `Locked | `Unlocked ] ->
    (string * [ `Original | `Renamed ], a) Bwv.t ->
    (a, b) ordered_termctx ->
    b Names.t
    * (string * [ `Original | `Renamed | `Locked ] * wrapped_parse option * wrapped_parse) Bwd.t =
 fun names lock vars ctx ->
  let merge_orig =
    match lock with
    | `Locked -> fun _ -> `Locked
    | `Unlocked -> fun o -> (o :> [ `Original | `Renamed | `Locked ]) in
  let module S = struct
    type t =
      (string * [ `Original | `Renamed | `Locked ] * wrapped_parse option * wrapped_parse) Bwd.t
  end in
  let module M = CubeOf.Monadic (Monad.State (S)) in
  match ctx with
  | Emp -> (names, Emp)
  | Lock ctx -> unparse_ctx names `Locked vars ctx
  | Ext (ctx, entry, af) -> (
      let vars, xs = Bwv.unappend af vars in
      let names, result = unparse_ctx names lock vars ctx in
      match entry with
      | Invis bindings ->
          (* We treat an invisible binding as consisting of all nameless variables, and autogenerate names for them all. *)
          let x, names = Names.add names (singleton_variables (CubeOf.dim bindings) None) in
          let do_binding (b : b binding) (res : S.t) : unit * S.t =
            let ty = Wrap (unparse names b.ty No.Interval.entire No.Interval.entire) in
            let tm =
              Option.map
                (fun t -> Wrap (unparse names t No.Interval.entire No.Interval.entire))
                b.tm in
            ((), Snoc (res, (top_variable x, `Renamed, tm, ty))) in
          let _, result =
            M.miterM { it = (fun _ [ b ] res -> do_binding b res) } [ bindings ] result in
          (names, result)
      | Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus } ->
          (* First we split off the field variables, if any. *)
          let xs, fs = Bwv.unappend fplus xs in
          (* Now we assemble the variable names we got from the uniquified variable list into a cube, iterating backwards so that the indices match those of the Bwv.  We ignore the variable names given in the context, but we use their cube to ensure statically that we got the right number of uniquified names.  *)
          let module T = struct
            type 'n t = (string * [ `Original | `Renamed ], 'n) Bwv.t
          end in
          let module Fold = NICubeOf.Traverse (T) in
          let do_var : type left m n.
              (m, n) sface ->
              (left, m, string option) NFamOf.t ->
              left N.suc T.t ->
              left T.t * (left, m, string * [ `Original | `Renamed ]) NFamOf.t =
           fun _ (NFamOf _) (Snoc (xs, x)) -> (xs, NFamOf x) in
          let _, vardata = Fold.fold_map_right { foldmap = do_var } vars xs in
          (* Then we project out the variable names alone.  TODO: Can we do this as part of the same iteration?  It would require a two-output version of the traversal.  *)
          let projector : type left m n.
              (m, n) sface ->
              (left, m, string * [ `Original | `Renamed ]) NFamOf.t ->
              (left, m, string) NFamOf.t =
           fun _ (NFamOf (x, _)) -> NFamOf x in
          let xs = NICubeOf.map { map = projector } vardata in
          (* With the variables projected out, we add them to the Names.t.  We use Names.unsafe_add because at this point the variables have already been uniquified by Names.uniquify_vars. *)
          let fnames =
            Bwv.mmap (fun [ (x, _); (f, _, _) ] -> (Field.to_string f, x)) [ fs; fields ] in
          let names = Names.unsafe_add names (Variables (dim, plusdim, xs)) (Bwv.to_bwd fnames) in
          (* Then we iterate forwards through the bindings, unparsing them with these names and adding them to the result. *)
          let do_binding fab (b : b binding) (res : S.t) : unit * S.t =
            match (hasfields, is_id_sface fab) with
            | Has_fields, Some _ -> ((), res)
            | _ ->
                let ty = Wrap (unparse names b.ty No.Interval.entire No.Interval.entire) in
                let tm =
                  Option.map
                    (fun t -> Wrap (unparse names t No.Interval.entire No.Interval.entire))
                    b.tm in
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus plusdim fab in
                let fastr = "." ^ string_of_sface fa in
                let add_fa =
                  match D.compare (cod_sface fa) D.zero with
                  | Eq -> fun y -> y
                  | Neq -> fun y -> y ^ fastr in
                let x, orig = NICubeOf.find vardata fb in
                let x = add_fa x in
                let res = Snoc (res, (x, merge_orig orig, tm, ty)) in
                ((), res) in
          let _, result =
            M.miterM { it = (fun fab [ b ] res -> do_binding fab b res) } [ bindings ] result in
          (* Finally, we iterate forwards through the fields as well, unparsing their types and adding them to the result also. *)
          let module M = Bwv.Monadic (Monad.State (S)) in
          let _, result =
            M.miterM
              (fun [ (x, orig); (_, _, ty) ] res ->
                let ty = Wrap (unparse names ty No.Interval.entire No.Interval.entire) in
                let res = Snoc (res, (x, merge_orig orig, None, ty)) in
                ((), res))
              [ fs; fields ] result in
          (names, result))

(* See the explanation of this function in Core.Reporter. *)
let () =
  let open PPrint in
  let open Print in
  Reporter.printer :=
    fun ~sort pr ->
      Reporter.try_with ~fatal:(fun d ->
          Reporter.Code.PrintingError.read () d.message;
          string "_UNPRINTABLE")
      @@ fun () ->
      Readback.Displaying.run ~env:true @@ fun () ->
      match pr with
      | PUnit -> empty
      | PInt i -> string (string_of_int i)
      | PString str -> utf8string str
      | PField f -> utf8string (Field.to_string f)
      | PConstr c -> utf8string (Constr.to_string c)
      | PLevel i -> string (Printf.sprintf "(%d,%d)" (fst i) (snd i))
      | PTerm (ctx, tm) ->
          pp_complete_term
            (Wrap (unparse (Names.of_ctx ctx) tm No.Interval.entire No.Interval.entire))
            `None
      | PVal (ctx, tm) ->
          pp_complete_term
            (Wrap
               (unparse (Names.of_ctx ctx) (readback_val ~sort ctx tm) No.Interval.entire
                  No.Interval.entire))
            `None
      | PNormal (ctx, tm) ->
          pp_complete_term
            (Wrap
               (unparse (Names.of_ctx ctx) (readback_nf ctx tm) No.Interval.entire
                  No.Interval.entire))
            `None
      | PConstant name -> utf8string (String.concat "." (Scope.name_of name))
      | PMeta v -> utf8string (Meta.name v)
      | PHole (origin, vars, Permute (p, ctx), ty) ->
          let run =
            match origin with
            (* If the hole comes from an earlier time, we rewind to that time before displaying, so that the correct notations and names will be in scope. *)
            | Instant instant when origin <> Origin.current () ->
                Origin.rewind_command_then_undo instant
            (* Otherwise, we give up.  Normally this would only happen when it's from the current origin (e.g. being created right now in a file) anyway. *)
            | _ -> fun f -> f () in
          run @@ fun () ->
          let vars, names = Names.uniquify_vars vars in
          let names, ctx = unparse_ctx names `Unlocked (Bwv.permute vars p) ctx in
          let ty = unparse names ty No.Interval.entire No.Interval.entire in
          pp_hole ctx (Wrap ty)
      | Dump.Val tm -> Dump.value tm
      | Dump.DeepVal (tm, n) -> Dump.dvalue n tm
      | Dump.Head h -> Dump.head h
      | Dump.Binder b -> Dump.binder b
      | Dump.Term tm -> Dump.term tm
      | Dump.Tel tm -> Dump.tel tm
      | Dump.Env e -> Dump.env e
      | Dump.DeepEnv (e, n) -> Dump.denv n e
      | Dump.Check e -> Dump.check e
      | Dump.Apps e -> Dump.apps e
      | Dump.Entry e -> Dump.entry e
      | Dump.OrderedCtx e -> Dump.ordered_ctx e
      | Dump.Ctx e -> Dump.ctx e
      | _ -> fatal (Anomaly "unknown printable")

(* Hack to ensure the above code is executed. *)
let install () = ()
