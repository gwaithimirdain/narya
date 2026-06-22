open Bwd
open Bwd.Infix
open Util
open Tbwd
open Bwd_extra
open Dim
open Modal
open Core
open Tctx
open Origin
open Term
open Notation
open Builtins
open Reporter
open Printable
open Range
open Readback
module StringMap = Map.Make (String)

(* Extract the top codomain term from a CodCube. *)
let cod_top : type mode modality n a.
    (n, mode * modality * a) CodCube.t -> (mode, (a, (modality, n) dim_entry) snoc, kinetic) term =
 fun cods ->
  let (CodFam.Cod t) = CodCube.find_top cods in
  t

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

let rec get_list : type mode n.
    (mode, n, kinetic) term -> (mode, n, kinetic) term Bwd.t -> (mode, n, kinetic) term Bwd.t option
    =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, []) when c = Constr.intern "nil" -> Some elts
  | Constr (c, _, [ Modal (carmod, carplus, car); Modal (cdrmod, cdrplus, cdr) ])
    when c = Constr.intern "cons" -> (
      (* Currently, only "cons" constructors with non-modal arguments can be printed using list syntax.  *)
      match (Modality.compare_id carmod, Modality.compare_id cdrmod) with
      | Eq, Eq ->
          let Plus_lock (Zero _, Zero), Plus_lock (Zero _, Zero) = (carplus, cdrplus) in
          get_list (CubeOf.find_top cdr) (Snoc (elts, CubeOf.find_top car))
      | _ -> None)
  | _ -> None

let rec get_bwd : type mode n.
    (mode, n, kinetic) term -> (mode, n, kinetic) term list -> (mode, n, kinetic) term Bwd.t option
    =
 fun tm elts ->
  match tm with
  | Term.Constr (c, _, []) when c = Constr.intern "emp" -> Some (Bwd.of_list elts)
  | Constr (c, _, [ Modal (rdcmod, rdcplus, rdc); Modal (racmod, racplus, rac) ])
    when c = Constr.intern "snoc" -> (
      (* Currently, only "snoc" constructors with non-modal arguments can be printed using bwd syntax.  *)
      match (Modality.compare_id racmod, Modality.compare_id rdcmod) with
      | Eq, Eq ->
          let Plus_lock (Zero _, Zero), Plus_lock (Zero _, Zero) = (racplus, rdcplus) in
          get_bwd (CubeOf.find_top rdc) (CubeOf.find_top rac :: elts)
      | _ -> None)
  | _ -> None

let rec synths : type mode n. (mode, n, kinetic) term -> bool = function
  | Var _ | Const _ | Meta _ | MetaEnv _ | Field _ | UU _ | Inst _ | Pi _ | App _ | Act _ | Let _ ->
      true
  (* TODO: Verify this after we add raw syntax for Key *)
  | Key _ -> true
  | Constr _ | Lam _ | Struct _ | Canonical_display _ -> false
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

(* Given a term, extract its head and arguments as an application spine.  If the spine contains a field projection, stop there and return only the arguments after it, noting the field name and what it is applied to (which itself be another spine).  We don't include the modality, since modalities are not printed with applications. *)
type (_, _) spine_arg =
  | Spine_arg :
      (('a, 'mode, 'modality, 'dom, 'an) plus_lock, ('a, 'an) Eq.t) Either.t
      * ('dom, 'an, 's) term
      * [ `Implicit | `Explicit ]
      -> ('a, 's) spine_arg

let rec get_spine : type mode a.
    (mode, a, kinetic) term ->
    [ `App of (mode, a, kinetic) term * (a, kinetic) spine_arg Bwd.t
    | `Field of (mode, a, kinetic) term * string * int list * (a, kinetic) spine_arg Bwd.t ] =
 fun tm ->
  match tm with
  | App
      ( fn,
        (* Modalities are not printed with applications *)
        Modal (type am) ((_modality, plus, arg) : _ * _ * (_, (_, am, kinetic) Term.term) CubeOf.t)
      ) -> (
      let module M = CubeOf.Monadic (Monad.State (struct
        type t = (a, kinetic) spine_arg Bwd.t
      end))
      in
      (* To append the entries in a cube to a Bwd, we iterate through it with a Bwd state. *)
      let append_bwd args =
        let all_args = not (synths (CubeOf.find_top arg)) in
        snd
          (M.miterM
             {
               it =
                 (fun fa [ (x : (_, am, kinetic) Term.term) ] s ->
                   match (Display.function_boundaries (), is_id_sface fa, all_args) with
                   | `Hide, None, false -> ((), s)
                   | _, None, _ -> ((), Snoc (s, Spine_arg (Left plus, x, `Implicit)))
                   | _ -> ((), Snoc (s, Spine_arg (Left plus, x, `Explicit))));
             }
             [ arg ] args) in
      match get_spine fn with
      | `App (head, args) -> `App (head, append_bwd args)
      | `Field (head, fld, ins, args) -> `Field (head, fld, ins, append_bwd args))
  | Field (head, fld, ins) -> `Field (head, Field.to_string fld, show_ins ins, Emp)
  (* We have to look through identity degeneracies and keys here. *)
  | Act (body, s, _) -> (
      match is_id_deg s with
      | Some _ -> get_spine body
      | None -> `App (tm, Emp))
  | Key { tm = body; cell; plus_src; plus_tgt } -> (
      match (Modalcell.compare_id cell, plus_tgt, plus_src) with
      | Eq, Plus_with_locks (Zero, Zero _), Plus_lock (Zero _, Zero) -> get_spine body
      | _ -> `App (tm, Emp))
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

(* The primary unparsing function.  Given the variable names, unparse a term into given tightness intervals. *)
let rec unparse : type mode n lt ls rt rs s.
    n Names.t ->
    (mode, n, s) term ->
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
  | UU (mode, n) -> unparse_universe vars mode n !universes li ri
  | Inst (ty, tyargs) -> unparse_inst vars ty vars tyargs li ri
  | Pi (_, Modal (_, _, doms), _) ->
      let arr, notn =
        match D.compare_zero (CubeOf.dim doms) with
        | Zero -> (`Arrow, arrow)
        | Pos _ -> (`DblArrow, dblarrow) in
      unparse_pis arr notn vars Emp tm li ri
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
  | Key { tm; cell; plus_tgt = Plus_with_locks (comp, _); plus_src } -> (
      (* We omit printing keys that are identities or unique, since they can be reconstructed on parse. *)
      match
        ( Modalcell.compare_id cell,
          Modalcell.find_unique (Modalcell.vsrc cell) (Modalcell.vtgt cell) )
      with
      | Eq, _ | _, Some (Unique _) ->
          unparse (Names.add_lock (Names.split vars comp) plus_src) tm li ri
      | Neq, None ->
          (* MODALTODO: Print keys *)
          fatal (Unimplemented "printing keys"))
  | Let (x, Modal (modality, plus, tm), body) -> (
      (match Modality.compare_id modality with
      | Eq -> ()
      (* MODALTODO:  *)
      | Neq -> fatal (Unimplemented "unparsing modal let-bindings"));
      let tm = unparse (Names.add_lock vars plus) tm No.Interval.entire No.Interval.entire in
      (* If a let-in doesn't fit in its interval, we have to parenthesize it. *)
      let x, vars = Names.add_cube D.zero vars (binder_name_of_option x) in
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
  | Lam (Variables (m, _, _), _, _) ->
      (* Modalities aren't printed on abstractions *)
      let cube =
        match D.compare m D.zero with
        | Eq -> `Normal
        | Neq -> `Cube in
      unparse_lam cube vars Emp tm li ri
  | Struct
      (type m et)
      ({ eta = Eta; fields; dim = _; energy = _ } : (mode, m, n, s, et) struct_args) ->
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
                               ((fld, structfield) :
                                 i Field.t * (i, _ * (m * n * s * et)) Structfield.t)) ->
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
          let args =
            of_list_map
              (* The modality isn't printed for constructor applications. *)
              (fun (Modal (_modality, plus, x)) ->
                make_unparser (Names.add_lock vars plus) (CubeOf.find_top x))
              args in
          unparse_spine vars (`Constr c) args li ri)
  | Realize tm -> unparse vars tm li ri
  | Canonical c -> unparse_canonical vars c li ri
  | Canonical_display d -> unparse_canonical_display vars d li ri
  | Struct { eta = Noeta; dim; fields; energy = _ } -> unparse_comatch vars dim fields li ri
  | Match { tm; dim; branches } -> unparse_match vars tm dim branches li ri
  | Unshift _ -> fatal (Unimplemented "unparsing unshifts")
  (* An Unact only changes the dimension/action, not which variables are in scope, so for display we can simply unparse its body. *)
  | Unact (_, tm) -> unparse vars tm li ri
  | Shift _ -> fatal (Unimplemented "unparsing shifts")
  | Weaken tm -> unparse (Names.remove vars Now) tm li ri

(* The master unparsing function can easily be delayed. *)
and make_unparser : type mode n. n Names.t -> (mode, n, kinetic) term -> unparser =
 fun vars tm -> { unparse = (fun li ri -> unparse vars tm li ri) }

(* A version that wraps implicit arguments in braces. *)
and make_unparser_implicit : type n. n Names.t -> (n, kinetic) spine_arg -> unparser =
 fun vars (Spine_arg (plus, tm, i)) ->
  let vars =
    match plus with
    | Left plus -> Names.add_lock vars plus
    | Right Eq -> vars in
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
and unparse_canonical : type mode n lt ls rt rs.
    n Names.t ->
    (mode, n) Term.canonical ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars c li ri ->
  match c with
  | Data { indices; constrs; discrete = _; hints = _ } ->
      let indexed =
        match indices with
        | Zero -> false
        | Suc _ -> true in
      unparse_data vars indexed constrs li ri
  | Codata { eta; dim; fields; _ } -> unparse_codata vars eta dim fields li ri

(* Unparse a codatatype (Noeta, "codata [ x .fld : ty | ... ]") or record type (Eta).  A codatatype, or a higher-dimensional record type (whose field types may reference the self-variable directly, e.g. Gel), uses a single self-variable and the "self record" surface syntax with explicit field projections, which handles dependence of later field types on earlier ones.  A zero-dimensional record type uses the field-variable surface syntax "sig ( a : ty, ... )", exposing the (anonymous) self-variable's fields as named variables, so that field-projections of the self read back as field variables. *)
and unparse_codata : type mode n a et lt ls rt rs.
    a Names.t ->
    (potential, et) eta ->
    n D.t ->
    (mode * a * n * et) Term.CodatafieldAbwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars eta _dim fields _li _ri ->
  (* Unparse the type of a single field, in a names-context that exposes the self-variable (and, for records, its fields). *)
  let field_ty : type i.
      (a, (mode id, n) dim_entry) snoc Names.t ->
      (i, mode * a * n * et) Term.Codatafield.t ->
      (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located =
   fun selfvars cf ->
    match cf with
    | Term.Codatafield.Lower tm -> unparse selfvars tm No.Interval.entire No.Interval.entire
    | Term.Codatafield.Higher _ -> fatal (Unimplemented "unparsing higher codata fields") in
  (* Self-variable ("self record") rendering, with explicit field projections: used for codatatypes, and as a fallback for records whose field types reference the self-variable directly. *)
  let self_var_render () =
    let x, selfvars = Names.add_cube _dim vars (`Anon no_hints) in
    match eta with
    | Noeta ->
        let inner =
          Bwd.fold_left
            (fun acc (Term.CodatafieldAbwd.Entry (fld, cf)) ->
              let pat = unparse_field_app x (Field.to_string fld) [] in
              acc <: mktok (Op "|") <: Term pat <: mktok Colon <: Term (field_ty selfvars cf))
            (Snoc (Emp, mktok LBracket))
            fields in
        unlocated (outfix ~notn:codata ~inner:(Multiple (wstok Codata, inner, wstok RBracket)))
    | Eta ->
        let inner, _ =
          Bwd.fold_left
            (fun (acc, first) (Term.CodatafieldAbwd.Entry (fld, cf)) ->
              let pat = unparse_field_app x (Field.to_string fld) [] in
              ( (if first then acc else acc <: mktok (Op ","))
                <: Term pat
                <: mktok Colon
                <: Term (field_ty selfvars cf),
                false ))
            (Snoc (Emp, mktok LParen), true)
            fields in
        unlocated (outfix ~notn:record ~inner:(Multiple (wstok Sig, inner, wstok RParen))) in
  match eta with
  | Noeta -> self_var_render ()
  | Eta -> (
      (* Try the field-variable syntax "sig (a : ..., b : a → ..., ...)", exposing the anonymous self-variable's fields as named variables.  We fall back to the self-variable syntax if a field name clashes with a name already in scope (add_fields returns None), or if a field type references the self-variable other than via a field projection ("Names.lookup" reports the Self_used bug, which we catch). *)
      Reporter.try_with ~fatal:(fun d ->
          match d.message with
          | Self_used -> self_var_render ()
          | _ -> fatal_diagnostic d)
      @@ fun () ->
      let field_names =
        Bwd.fold_left
          (fun acc (Term.CodatafieldAbwd.Entry (fld, _)) -> acc @ [ Field.to_string fld ])
          [] fields in
      match Names.add_fields _dim vars field_names with
      | None -> self_var_render ()
      | Some (selfvars, var_names) ->
          let inner, _, _ =
            Bwd.fold_left
              (fun (acc, first, var_names) (Term.CodatafieldAbwd.Entry (_, cf)) ->
                let var_name, var_names =
                  match var_names with
                  | v :: vs -> (v, vs)
                  | [] -> ("", []) in
                let pat = unlocated (Ident ([ var_name ], [])) in
                ( (if first then acc else acc <: mktok (Op ","))
                  <: Term pat
                  <: mktok Colon
                  <: Term (field_ty selfvars cf),
                  false,
                  var_names ))
              (Snoc (Emp, mktok LParen), true, var_names)
              fields in
          unlocated (outfix ~notn:record ~inner:(Multiple (wstok Sig, inner, wstok RParen))))

(* Unparse the argument telescope of a datatype constructor as a Bwd of "(x : A)" pi-domain unparsers, returning also the name context extended by the telescope variables. *)
and unparse_tel_args : type mode b bc cc.
    b Names.t -> (mode, b, cc, bc) Term.tel -> unparser Bwd.t -> bc Names.t * unparser Bwd.t =
 fun vars tel acc ->
  match tel with
  | Emp -> (vars, acc)
  | Ext (name, Modal (modality, plus, ty), rest) ->
      let uty = unparse (Names.add_lock vars plus) ty No.Interval.entire No.Interval.entire in
      let x, newvars = Names.add_cube D.zero vars (binder_name_of_option name) in
      unparse_tel_args newvars rest
        (acc <: { unparse = (fun _ _ -> unparse_pi_dom x (Modality.name modality) uty) })

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

(* Unparse a datatype "data [ | constr. (x:A) ... | ... ]" from a term-level datatype.  The output type of each constructor is shown only for indexed datatypes (the caller passes whether the datatype is indexed). *)
and unparse_data : type mode a lt ls rt rs.
    a Names.t ->
    bool ->
    (Constr.t, (mode, a) Term.dataconstr) Abwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars indexed constrs _li _ri ->
  let inner =
    Bwd.fold_left
      (fun acc (c, dc) ->
        let cterm = unparse_dataconstr vars indexed c dc No.Interval.entire No.Interval.entire in
        acc <: mktok (Op "|") <: Term cterm)
      (Snoc (Emp, mktok LBracket))
      constrs in
  unlocated (outfix ~notn:data ~inner:(Multiple (wstok Data, inner, wstok RBracket)))

and unparse_dataconstr : type mode a lt ls rt rs.
    a Names.t ->
    bool ->
    Constr.t ->
    (mode, a) Term.dataconstr ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars indexed c (Dataconstr { args; output }) li ri ->
  let bcvars, argunps = unparse_tel_args vars args Emp in
  (* Show the output type only for indexed datatypes; the stored output already includes the real datatype head and indices. *)
  let output_display =
    if indexed then Some { unparse = (fun li ri -> unparse bcvars output li ri) } else None in
  unparse_constr_display c argunps output_display li ri

(* Render a display-only canonical-declaration node (produced by readback for "about"): purely syntactic assembly of already-read-back constructor displays into "data [ … ]". *)
and unparse_canonical_display : type mode a lt ls rt rs.
    a Names.t ->
    (mode, a) Term.canonical_display ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars cd _li _ri ->
  match cd with
  | Data_display constrs ->
      let inner =
        Bwd.fold_left
          (fun acc (c, dcd) ->
            let cterm =
              match dcd with
              | Term.Tel_constr (tel, output) ->
                  let bcvars, argunps = unparse_tel_args vars tel Emp in
                  let output =
                    Option.map
                      (fun out -> { unparse = (fun li ri -> unparse bcvars out li ri) })
                      output in
                  unparse_constr_display c argunps output No.Interval.entire No.Interval.entire
              | Term.Pi_constr fn ->
                  let output = { unparse = (fun li ri -> unparse vars fn li ri) } in
                  unparse_constr_display c Emp (Some output) No.Interval.entire No.Interval.entire
            in
            acc <: mktok (Op "|") <: Term cterm)
          (Snoc (Emp, mktok LBracket))
          constrs in
      unlocated (outfix ~notn:data ~inner:(Multiple (wstok Data, inner, wstok RBracket)))
  | Codata_display { eta; dim = mk; fields } -> (
      (* Assemble the codata or record notation, matching the field-instance display of a value-level codatatype.  A record (eta) is displayed with the field-variable syntax, unless some field type references the self-variable other than via a field projection (e.g. a higher record like Gel, whose field types use the self's faces directly) — which the field-variable syntax cannot express — in which case "Names.lookup" raises Self_used and we fall back to the self-variable syntax. *)
      let self_var_render () =
        (* Introduce a single self-variable cube of the codatatype's dimension; readback produced the field types relative to this self-variable.  Each non-projectable instance's type lives in a context degenerated by its remaining dimension, whose names we reconstruct with Names.degenerate. *)
        let selfname, selfnames = Names.add_cube mk vars (`Anon no_hints) in
        let display_field : type i.
            string list ->
            i Field.t ->
            (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located ->
            (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located
            * (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located =
         fun suffix fld ty -> (unparse_field_app selfname (Field.to_string fld) suffix, ty) in
        let instances =
          Bwd.fold_left
            (fun acc entry ->
              match entry with
              | Term.Cfd (fld, suffix, tm) ->
                  acc
                  <: display_field suffix fld
                       (unparse selfnames tm No.Interval.entire No.Interval.entire)
              | Term.Cfd_deg (fld, suffix, r, plusmap, tm) ->
                  let dnames = Names.degenerate r plusmap selfnames in
                  acc
                  <: display_field suffix fld
                       (unparse dnames tm No.Interval.entire No.Interval.entire))
            Emp fields in
        match eta with
        | Noeta ->
            let inner =
              Bwd.fold_left
                (fun acc (pat, ty) -> acc <: mktok (Op "|") <: Term pat <: mktok Colon <: Term ty)
                (Snoc (Emp, mktok LBracket))
                instances in
            unlocated (outfix ~notn:codata ~inner:(Multiple (wstok Codata, inner, wstok RBracket)))
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
            unlocated (outfix ~notn:record ~inner:(Multiple (wstok Sig, inner, wstok RParen))) in
      match eta with
      | Noeta -> self_var_render ()
      | Eta -> (
          (* A record type has only (projectable, lower) fields, displayed with the field-variable syntax "sig (a : ..., b : a → ..., ...)": we introduce an anonymous self-variable with its fields exposed as named variables, so that the field types' projections of the self read back as field variables.  We fall back to the self-variable syntax if a field name clashes with a name already in scope (add_fields returns None), or if a field type uses the self directly (the Self_used bug, which we catch). *)
          Reporter.try_with ~fatal:(fun d ->
              match d.message with
              | Self_used -> self_var_render ()
              | _ -> fatal_diagnostic d)
          @@ fun () ->
          let field_names =
            Bwd.fold_left
              (fun acc entry ->
                match entry with
                | Term.Cfd (fld, _, _) -> acc @ [ Field.to_string fld ]
                | Term.Cfd_deg (fld, _, _, _, _) -> acc @ [ Field.to_string fld ])
              [] fields in
          match Names.add_fields mk vars field_names with
          | None -> self_var_render ()
          | Some (selfnames, var_names) ->
              let inner, _, _ =
                Bwd.fold_left
                  (fun (acc, first, var_names) entry ->
                    let var_name, var_names =
                      match var_names with
                      | v :: vs -> (v, vs)
                      | [] -> ("", []) in
                    let pat = unlocated (Ident ([ var_name ], [])) in
                    let ty =
                      match entry with
                      | Term.Cfd (_, _, tm) ->
                          unparse selfnames tm No.Interval.entire No.Interval.entire
                      | Term.Cfd_deg (_, _, r, plusmap, tm) ->
                          let dnames = Names.degenerate r plusmap selfnames in
                          unparse dnames tm No.Interval.entire No.Interval.entire in
                    ( (if first then acc else acc <: mktok (Op ","))
                      <: Term pat
                      <: mktok Colon
                      <: Term ty,
                      false,
                      var_names ))
                  (Snoc (Emp, mktok LParen), true, var_names)
                  fields in
              unlocated (outfix ~notn:record ~inner:(Multiple (wstok Sig, inner, wstok RParen)))))

(* Unparse a match "match tm [ | constr. x ... |-> body | ... ]".  Refuted branches are omitted; an all-refuted (or empty) match prints as "match tm [ ]". *)
and unparse_match : type mode n m lt ls rt rs.
    n Names.t ->
    (mode, n, kinetic) term ->
    m D.t ->
    (mode, n, m) Term.branch Constr.Map.t ->
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
        | Term.Branch { annotate; comp; perm; tm = body } ->
            (* Extend the name context by the branch's pattern variables (named via the stored "annotate" witness), then permute it to the body's context. *)
            let abvars, xs = Names.add_match_vars vars annotate comp in
            let bodyvars = Names.permute perm abvars in
            let args =
              Bwd.of_list (List.map (fun x -> { unparse = (fun _ _ -> unparse_var x) }) xs) in
            let pat = unparse_spine vars (`Constr c) args No.Interval.entire No.Interval.entire in
            let ubody = unparse bodyvars body No.Interval.entire No.Interval.entire in
            acc <: mktok (Op "|") <: Term pat <: mktok mapsto <: Term ubody)
      branches
      (Snoc (Emp, Term disc) <: mktok LBracket) in
  unlocated (outfix ~notn:implicit_mtch ~inner:(Multiple (wstok Match, inner, wstok RBracket)))

(* Unparse a comatch "[ .fld |-> body | ... ]".  An empty comatch prints with the empty (co)match notation. *)
and unparse_comatch : type mode n a s et lt ls rt rs.
    a Names.t ->
    n D.t ->
    (mode * (n * a * s * et)) Term.StructfieldAbwd.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars dim fields _li _ri ->
  (* Render the instances of a higher field: one per partial bijection between the comatch's dimension and the field's intrinsic dimension, exactly as the codatatype declaration lists them.  Each body was read back in a context degenerated by the partial bijection's remaining dimensions, recorded by the plus-map stored alongside it, so we degenerate the names to match before unparsing it (cf. the codata-declaration display). *)
  let higher_fields : type i.
      observation Bwd.t -> i Field.t -> (n, i, mode * a) Term.PlusPbijmap.t -> observation Bwd.t =
   fun acc fld pbijmap ->
    Seq.fold_left
      (fun acc (Pbij_between (pbij : (n, i, _) pbij)) ->
        match Term.PlusPbijmap.find pbij pbijmap with
        | None -> acc
        | Some (Term.PlusFam.PlusFam (plusmap, body)) ->
            let dnames = Names.degenerate (remaining pbij) plusmap vars in
            let pat = unlocated (Field (Field.to_string fld, strings_of_pbij pbij, [])) in
            let ubody = unparse dnames body No.Interval.entire No.Interval.entire in
            acc <: mktok (Op "|") <: Term pat <: mktok Mapsto <: Term ubody)
      acc
      (all_pbij_between dim (Field.dim fld)) in
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
                  ((fld, sf) : i Field.t * (i, mode * (n * a * s * et)) Term.Structfield.t)) ->
            match sf with
            | Term.Structfield.Lower (tm, _) ->
                let pat = unlocated (Field (Field.to_string fld, [], [])) in
                let ubody = unparse vars tm No.Interval.entire No.Interval.entire in
                acc <: mktok (Op "|") <: Term pat <: mktok Mapsto <: Term ubody
            | Term.Structfield.Higher pbijmap -> higher_fields acc fld pbijmap
            | Term.Structfield.LazyHigher pbijmap -> higher_fields acc fld (Lazy.force pbijmap))
          Emp fields in
      unlocated (outfix ~notn:comatch ~inner:(Multiple (wstok LBracket, inner, wstok RBracket)))

(* Unparse a spine with its arguments whose head could be many things: an as-yet-not-unparsed term, a constructor, a field projection, a degeneracy, or a general delayed unparsing. *)
and unparse_spine : type mode n lt ls rt rs.
    n Names.t ->
    [ `Term of (mode, n, kinetic) term
    | `Constr of Constr.t
    | `Field of (mode, n, kinetic) term * string * int list
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

and unparse_field : type mode n lt ls rt rs.
    n Names.t ->
    (mode, n, kinetic) term ->
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

and unparse_field_var : type mode n lt ls rt rs.
    n Names.t -> (mode, n, kinetic) term -> string -> (lt, ls, rt, rs) parse located option =
 fun vars tm fld ->
  match tm with
  | Var x -> (
      match Names.lookup_field vars x fld with
      (* If the field got used up by the lookup, we just return the variable. *)
      | Some name -> Some (unlocated (Ident (name, [])))
      (* If the field is still leftover after the lookup, we unparse it as a field. *)
      | None -> None)
  (* TODO: Nonidentity degeneracies and keys of field variables should still be field variables, but with the degeneracies and keys on the outside.  Currently we just fail if there is a nonidentity degeneracy or key, probably leading to printing the unnamed self variable. *)
  | Act (tm, deg, _) -> (
      match is_id_deg deg with
      | Some _ -> unparse_field_var vars tm fld
      | None -> None)
  | Key { tm; cell; plus_src; plus_tgt = Plus_with_locks (comp, _) } -> (
      match Modalcell.compare_id cell with
      | Eq -> unparse_field_var (Names.add_lock (Names.split vars comp) plus_src) tm fld
      | Neq -> None)
  | _ -> None

and unparse_universe : type mode n k lt ls rt rs.
    n Names.t ->
    mode Mode.t ->
    k D.t ->
    (string * Mode.wrapped * (closed, No.plus_omega, closed) notation) list ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars mode n uus li ri ->
  match uus with
  | [] -> fatal (Anomaly ("universe not found for mode" ^ Mode.name mode))
  | (name, Wrap umode, universe) :: uus -> (
      match Mode.compare mode umode with
      | Eq ->
          unparse_act ~sort:(`Type, `Canonical) vars
            {
              unparse =
                (fun _ _ ->
                  unlocated (outfix ~notn:universe ~inner:(Single (wstok (Ident [ name ])))));
            }
            (deg_zero n) li ri
      | Neq -> unparse_universe vars mode n uus li ri)

(* For unparsing an iterated abstraction, we group together the fully-normal variables and at-least-partially-cube variables, since they have different notations.  There is no notation for partially-cube variables, so we make them fully cube.  We recursively descend through the structure of the term, storing in 'cube' which kind of variable we are picking up and continuing until we find either a non-abstraction or an abstraction of the wrong type.  *)
and unparse_lam : type mode n lt ls rt rs s.
    [ `Cube | `Normal ] ->
    n Names.t ->
    (string * [ `Explicit | `Implicit ]) Bwd.t ->
    (mode, n, s) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun cube vars xs body li ri ->
  (* Modalities are not printed in abstractions *)
  match body with
  | Lam ((Variables (m, _, _) as boundvars), _modality, inner) -> (
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
and unparse_lam_done : type mode n lt ls rt rs s.
    [ `Cube | `Normal ] ->
    n Names.t ->
    (string * [ `Explicit | `Implicit ]) Bwd.t ->
    (mode, n, s) term ->
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
and unparse_numeral : type mode n. (mode, n, kinetic) term -> unparser option =
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
  let rec getsucs : type m c. (m, c, kinetic) term -> int -> unparser option =
   fun tm k ->
    match tm with
    | Term.Constr (c, dim, []) when c = zero -> make_numeral dim k
    | Term.Constr (c, dim, []) when c = one -> make_numeral dim (k + 1)
    | Constr (c, _, [ Modal (modality, _, arg) ]) when c = suc -> (
        (* Currently, only "suc" constructors with non-modal argument can be displayed as numerals. *)
        match Modality.compare_id modality with
        | Eq -> getsucs (CubeOf.find_top arg) (k + 1)
        | Neq -> None)
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
and unparse_inst : type mode n n' lt ls rt rs m k mk.
    (* We allow the type and its instantiation arguments to be in different contexts, for use in unparse_higher_pi. *)
    n Names.t ->
    (mode, n, kinetic) term ->
    n' Names.t ->
    (m, k, mk, (mode, n', kinetic) term) TubeOf.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars ty argvars tyargs li ri ->
  match (D.compare_zero (TubeOf.uninst tyargs), D.compare_zero (TubeOf.inst tyargs), ty) with
  (* A fully instantiated higher pi-type we can unparse prettily. *)
  | Zero, Pos _, Pi (x, Modal (modality, plus, doms), cods) -> (
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Eq ->
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (TubeOf.inst tyargs)) in
          let tyargs = TubeOf.mmap { map = (fun _ [ x ] -> Names.Named (argvars, x)) } [ tyargs ] in
          unparse_higher_pi vars Emp x modality plus doms cods tyargs li ri
      | Neq ->
          fatal (Dimension_mismatch ("unparsing higher pi", TubeOf.inst tyargs, CubeOf.dim doms)))
  | _ ->
      let tyargs = TubeOf.mmap { map = (fun _ [ x ] -> Names.Named (argvars, x)) } [ tyargs ] in
      unparse_named_inst vars ty tyargs li ri

and unparse_named_inst : type mode n lt ls rt rs m k mk.
    n Names.t ->
    (mode, n, kinetic) term ->
    (m, k, mk, mode Names.named_term) TubeOf.t ->
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
            | Some () ->
                ((), Snoc (s, make_unparser_implicit xvars (Spine_arg (Right Eq, x, `Explicit))))
            | None -> (
                (* We include it implicitly if display of type boundaries is on. *)
                match Display.type_boundaries () with
                | `Show ->
                    ((), Snoc (s, make_unparser_implicit xvars (Spine_arg (Right Eq, x, `Implicit))))
                | `Hide ->
                    (* We also include it implicitly if its codimension-1 envelope is non-synthesizing *)
                    let (Tface_of fa1) = codim1_envelope fa in
                    let (Named (_, x1)) = TubeOf.find tyargs fa1 in
                    if synths x1 then ((), s)
                    else
                      ( (),
                        Snoc (s, make_unparser_implicit xvars (Spine_arg (Right Eq, x, `Implicit)))
                      )));
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
and unparse_pis : type mode a lt ls rt rs.
    [ `Arrow | `DblArrow ] ->
    (No.strict opn, No.zero, No.nonstrict opn) notation ->
    a Names.t ->
    unparser Bwd.t ->
    (mode, a, kinetic) term ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun dim notn vars accum tm li ri ->
  match tm with
  | Pi (x, Modal (modality, plus, doms), cods) -> (
      match (D.compare_zero (CubeOf.dim doms), dim) with
      | Zero, `Arrow | Pos _, `DblArrow -> (
          (* Nontrivially modal pi-types are always printed dependently *)
          match (top_variable x, Modality.compare_id modality) with
          | (`Anon _ as anon), Eq ->
              (* non-dependent pi-type *)
              let _, newvars = Names.add vars (singleton_variables (CubeOf.dim doms) anon) in
              let dim =
                match dim with
                | `Arrow -> `Arrow None
                | `DblArrow -> `DblArrow in
              unparse_pis_final dim notn vars accum
                {
                  unparse =
                    (fun li ri ->
                      unparse_arrow dim notn
                        (make_unparser (Names.add_lock vars plus) (CubeOf.find_top doms))
                        (make_unparser newvars (cod_top cods))
                        li ri);
                }
                li ri
          | x, _ ->
              (* dependent pi-type *)
              let Variables (_, _, x), newvars =
                Names.add vars (singleton_variables (CubeOf.dim doms) x) in
              unparse_pis dim notn newvars
                (Snoc
                   ( accum,
                     {
                       unparse =
                         (fun _ _ ->
                           unparse_pi_dom (NICubeOf.find_top x) (Modality.name modality)
                             (unparse (Names.add_lock vars plus) (CubeOf.find_top doms)
                                No.Interval.entire No.Interval.entire));
                     } ))
                (cod_top cods) li ri)
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
    string list ->
    (No.minus_omega, No.nonstrict, No.minus_omega, No.nonstrict) parse located ->
    (lt, ls, rt, rs) parse located =
 fun ?(implicit = false) x modality dom ->
  let ldelim, rdelim = if implicit then (Token.LBrace, Token.RBrace) else (LParen, RParen) in
  let obs = Emp <: Term (unlocated (Ident ([ x ], []))) <: mktok Colon in
  let obs =
    match modality with
    | [] -> obs
    | m :: ms ->
        let fn = unlocated (Ident ([ m ], [])) in
        let left_ok, right_ok = (No.le_refl No.plus_omega, No.le_refl No.plus_omega) in
        let modalities =
          List.fold_left
            (fun fn m ->
              unlocated (App { fn; arg = unlocated (Ident ([ m ], [])); left_ok; right_ok }))
            fn ms in
        obs <: Term modalities <: mktok (Op "|") in
  unlocated (outfix ~notn:ascvar ~inner:(Multiple (wstok ldelim, obs <: Term dom, wstok rdelim)))

and unparse_higher_pi : type dom modality mode a am lt ls rt rs n.
    a Names.t ->
    unparser Bwd.t ->
    n variables ->
    (dom, modality, mode) Modality.t ->
    (a, mode, modality, dom, am) plus_lock ->
    (n, (dom, am, kinetic) term) CubeOf.t ->
    (n, mode * modality * a) CodCube.t ->
    (D.zero, n, n, mode Names.named_term) TubeOf.t ->
    (lt, ls) No.iinterval ->
    (rt, rs) No.iinterval ->
    (lt, ls, rt, rs) parse located =
 fun vars accum xs modality plus doms cods tyargs li ri ->
  let n = CubeOf.dim doms in
  (* Make all the variables ordinary ones by suffixing them with face names *without* a separating ".", and making sure that they all have some name. *)
  let xs, newvars = Names.add_full vars xs in
  let (Has_plus_lock xsplus) = plus_lock modality in
  let lockedvars = Names.add_lock newvars xsplus in
  (* Unparse each domain, instantiate it at the appropriate variables corresponding to its faces, and parenthesize or brace it to become a pi-type domain, adding them all to the accumulated list of domains. *)
  let module S = Monad.State (struct
    type t = unparser Bwd.t
  end) in
  let module MOf = CubeOf.Monadic (S) in
  let (), accum =
    MOf.miterM
      {
        it =
          (fun s [ (dom : (dom, am, kinetic) term) ] accum ->
            let k = dom_sface s in
            let x = find_variable s xs in
            let xargs =
              TubeOf.build D.zero (D.zero_plus k)
                { build = (fun fa -> Var (Index (Now, comp_sface s (sface_of_tface fa), xsplus))) }
            in
            let implicit = Option.is_none (is_id_sface s) in
            (* Here we use the flexibility allowed by unparse_inst to have the type and the instantiation arguments in different contexts, since the type is not in the context extended by the new variables.  However, it's important that we get the context for the type by *removing* those new variables from newvars, rather than using the original vars, since that retains the extra information stored in a Names.t about how many copies of a variable there have been, for future renaming use.  *)
            let dom =
              unparse_inst
                (Names.add_lock (Names.remove newvars Now) plus)
                dom lockedvars xargs No.Interval.entire No.Interval.entire in
            let m = Modality.name modality in
            ((), Snoc (accum, { unparse = (fun _ _ -> unparse_pi_dom ~implicit x m dom) })));
      }
      [ doms ] accum in
  (* The instantiation arguments 'tyargs' should already all be eta-expanded, since readback eta-expands the instantiation arguments of higher pi-types.  So we can descend into those abstractions and add the appropriate variables on which they depend to their unparsing contexts. *)
  let tyargs =
    let map : type k. (k, D.zero, n, n) tface -> mode Names.named_term -> mode Names.named_term =
     fun s (Names.Named (type b) ((lamvars, lam) : b Names.t * (mode, b, kinetic) term)) ->
      let k = dom_tface s in
      let lam_xs = sub_variables (sface_of_tface s) xs in
      let _, (lamvars : (b, (modality, k) dim_entry) snoc Names.t) =
        Names.add_strings lamvars lam_xs in
      match lam with
      | Lam (ys, lammod, body) -> (
          match (D.compare (dim_variables ys) k, Modality.compare lammod modality) with
          | Eq, Eq -> Named (lamvars, body)
          | Neq, _ -> fatal (Dimension_mismatch ("unparse_higher_pi lam", dim_variables ys, k))
          | _, Neq ->
              fatal (Modality_mismatch (`Internal, "unparse_higher_pi lam", lammod, modality)))
      | nonlam ->
          (* This case happens when we are recursively working with the domains of another higher pi-type. *)
          let (Has_plus_lock plusm) = plus_lock modality in
          let lamargs = CubeOf.build k { build = (fun s -> Var (Index (Now, s, plusm))) } in
          Named (lamvars, App (Weaken nonlam, Modal (modality, plusm, lamargs))) in
    TubeOf.mmap { map = (fun s [ lam ] -> map s lam) } [ tyargs ] in
  (* We only need the top codomain. *)
  match cod_top cods with
  | Pi (newxs, Modal (newmodality, newplus, newdoms), newcods) -> (
      (* If it's another pi-type, it must be of the same dimension since it is an (uninstantiated!) n-dimensional type, and we continue recursively. *)
      match D.compare (CubeOf.dim newdoms) n with
      | Eq -> unparse_higher_pi newvars accum newxs newmodality newplus newdoms newcods tyargs li ri
      | Neq -> fatal (Dimension_mismatch ("unparse_higher_pi recursion", CubeOf.dim newdoms, n)))
  (* It might also be a *partially* instantiated *higher* dimensional pi-type, in which case we combine the instantiation arguments to make it fully instantiated.  We don't continue accumulating domains as in the previous case, though, because in this case the codomain has different dimension, and hence needs its own arrow. *)
  | Inst (Pi (newxs, Modal (newmodality, newplus, newdoms), newcods), newtyargs) -> (
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
                (fun li ri ->
                  unparse_higher_pi newvars Emp newxs newmodality newplus newdoms newcods plustyargs
                    li ri);
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
let rec unparse_ctx : type dom modality mode a b.
    Names.uniquified_vars ->
    (dom, modality, mode) Modality.t ->
    (string * [ `Original | `Renamed ], a) Bwv.t ->
    (mode, a, b) ordered_termctx ->
    b Names.t * Print.printed_entry Bwd.t =
 fun names lock vars ctx ->
  let module S = struct
    type t = Print.printed_entry Bwd.t
  end in
  let module M = CubeOf.Monadic (Monad.State (S)) in
  match ctx with
  | Emp _ -> (Names.of_uniquified_vars names, Emp)
  | Lock (ctx, newlock) ->
      let (Comp ll) = Modality.comp lock in
      let names, out = unparse_ctx names (Modality.comp_out (Modality.of_gen newlock) ll) vars ctx in
      (Names.add_lock names (plus_lock_suc (plus_no_lock (Modality.Gen.tgt newlock)) newlock), out)
  | Parametric_lock ctx -> unparse_ctx names lock vars ctx
  | Ext
      (type edom emod a' x b' bm n)
      ((ctx, entry, af) :
        (mode, a', b') ordered_termctx
        * (edom, emod, mode, b', bm, x, n) Term.entry
        * (a', x, a) N.plus) -> (
      let vars, xs = Bwv.unappend af vars in
      let names, result = unparse_ctx names lock vars ctx in
      match entry with
      | Invis (plus_lock, bindings, hints) ->
          let modality = Modality.name (plus_lock_modality plus_lock) in
          (* We treat an invisible binding as consisting of all nameless variables, and autogenerate names for them all, using any display hints recorded from their types at readback time. *)
          let x, names = Names.add names (singleton_variables (CubeOf.dim bindings) (`Anon hints)) in
          let xnames = Names.add_lock names plus_lock in
          let do_binding (b : (edom, bm) binding) (res : S.t) : unit * S.t =
            let ty = Wrap (unparse xnames b.ty No.Interval.entire No.Interval.entire) in
            let tm =
              Option.map
                (fun t -> Wrap (unparse xnames t No.Interval.entire No.Interval.entire))
                b.tm in
            let lock = Modality.name lock in
            let var = top_variable x in
            ((), Snoc (res, { var; modality; renamed = true; lock; tm; ty })) in
          let _, result =
            M.miterM { it = (fun _ [ b ] res -> do_binding b res) } [ bindings ] result in
          (names, result)
      | Vis { dim; plusdim; vars; plus_lock; bindings; hasfields; fields; fplus } ->
          let modality = Modality.name (plus_lock_modality plus_lock) in
          (* First we split off the field variables, if any. *)
          let xs, fs = Bwv.unappend fplus xs in
          (* Now we assemble the variable names we got from the uniquified variable list into a cube, iterating backwards so that the indices match those of the Bwv.  We ignore the variable names given in the context, but we use their cube to ensure statically that we got the right number of uniquified names.  *)
          let module T = struct
            type 'n t = (string * [ `Original | `Renamed ], 'n) Bwv.t
          end in
          let module Fold = NICubeOf.Traverse (T) in
          let do_var : type left m n.
              (m, n) sface ->
              (left, m, binder_name) NFamOf.t ->
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
          let xnames = Names.add_lock names plus_lock in
          let lock = Modality.name lock in
          (* Then we iterate forwards through the bindings, unparsing them with these names and adding them to the result. *)
          let do_binding fab (b : (edom, bm) binding) (res : S.t) : unit * S.t =
            match (hasfields, is_id_sface fab) with
            | Has_fields, Some _ -> ((), res)
            | _ ->
                let ty = Wrap (unparse xnames b.ty No.Interval.entire No.Interval.entire) in
                let tm =
                  Option.map
                    (fun t -> Wrap (unparse xnames t No.Interval.entire No.Interval.entire))
                    b.tm in
                let (SFace_of_plus (_, fa, fb)) = sface_of_plus plusdim fab in
                let fastr = "." ^ string_of_sface fa in
                let add_fa =
                  match D.compare (cod_sface fa) D.zero with
                  | Eq -> fun y -> y
                  | Neq -> fun y -> y ^ fastr in
                let x, orig = NICubeOf.find vardata fb in
                let x = add_fa x in
                let renamed =
                  match orig with
                  | `Renamed -> true
                  | `Original -> false in
                let res = Snoc (res, { var = x; modality; renamed; lock; tm; ty }) in
                ((), res) in
          let _, result =
            M.miterM { it = (fun fab [ b ] res -> do_binding fab b res) } [ bindings ] result in
          (* Finally, we iterate forwards through the fields as well, unparsing their types and adding them to the result also. *)
          let module M = Bwv.Monadic (Monad.State (S)) in
          let _, result =
            M.miterM
              (fun [ (x, orig); (_, _, ty) ] res ->
                let ty = Wrap (unparse xnames ty No.Interval.entire No.Interval.entire) in
                let renamed =
                  match orig with
                  | `Renamed -> true
                  | `Original -> false in
                let res = Snoc (res, { var = x; modality; renamed; lock; tm = None; ty }) in
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
      | PAnd (x, y) -> print x ^^ utf8string " and " ^^ print y
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
      | PHole (origin, vars, (Permute (p, ctx) as termctx), ty) ->
          let run =
            match origin with
            (* If the hole comes from an earlier time, we rewind to that time before displaying, so that the correct notations and names will be in scope. *)
            | Instant instant when origin <> Origin.current () ->
                Origin.rewind_command_then_undo instant
            (* Otherwise, we give up.  Normally this would only happen when it's from the current origin (e.g. being created right now in a file) anyway. *)
            | _ -> fun f -> f () in
          run @@ fun () ->
          let vars, names = Names.uniquify_vars (hole_vars termctx vars) in
          let names, ctx =
            unparse_ctx names (Modality.id (Termctx.ordered_mode ctx)) (Bwv.permute vars p) ctx
          in
          let ty = unparse names ty No.Interval.entire No.Interval.entire in
          pp_hole ctx (Wrap ty)
      | PModality m -> utf8string (Modality.to_string m)
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
