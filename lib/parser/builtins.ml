open Util
open Compile
open Notations
open Core
open Raw
open Monad.Ops (Monad.Maybe)

let parens =
  make ~name:"()" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop LParen (term RParen (Done n)))

let () =
  add_compiler parens
    {
      compile =
        (fun ctx obs ->
          let body, obs = get_term obs in
          let () = get_done obs in
          compile ctx body);
    }

(* We could do this without flags, using two different notations. *)
type flag += Unasc_let | Asc_let

(* Let-in doesn't need to be right-associative in order to chain, because it is left-closed.  Declaring it to be nonassociative means that "let x := y in z : A" doesn't parse without parentheses, which I think is best as it looks ambiguous.  (The same idea applies to abstractions, although they are built into the parser rather than defined as mixfix notations.) *)
let letin =
  make ~name:"let" ~tightness:Float.neg_infinity ~left:Closed ~right:Open ~assoc:Non ~tree:(fun n ->
      eop Let
        (name
           (ops
              [
                (Coloneq, Flag (Unasc_let, term In (Done n)));
                (Colon, Flag (Asc_let, term Coloneq (term In (Done n))));
              ])))

let () =
  add_compiler letin
    {
      compile =
        (fun ctx obs ->
          let x, obs = get_name obs in
          let f = get_flag [ Unasc_let; Asc_let ] obs in
          match f with
          | Some Unasc_let -> (
              let term, obs = get_term obs in
              let body, obs = get_term obs in
              let () = get_done obs in
              let* term = compile ctx term in
              let* body = compile (Snoc (ctx, x)) body in
              match (term, body) with
              | Synth term, Synth body -> return (Synth (Let (term, body)))
              | _ -> None)
          | Some Asc_let -> (
              let ty, obs = get_term obs in
              let term, obs = get_term obs in
              let body, obs = get_term obs in
              let () = get_done obs in
              let* term = compile ctx term in
              let* ty = compile ctx ty in
              let* body = compile (Snoc (ctx, x)) body in
              match body with
              | Synth body -> return (Synth (Let (Asc (term, ty), body)))
              | _ -> None)
          | _ -> raise (Failure "Unrecognized flag"));
    }

(* Is there any way to avoid these flags too?  If so, we could simplify by getting rid of flags completely. *)
type flag += Implicit_pi | Explicit_pi | Default_pi

let pi =
  make ~name:"pi" ~tightness:0. ~left:Closed ~right:Open ~assoc:Right ~tree:(fun n ->
      let rec explicit_pi () = Flag (Explicit_pi, name (explicit_pi_vars ()))
      and implicit_pi () = Flag (Implicit_pi, name (implicit_pi_vars ()))
      and explicit_pi_vars () =
        Inner
          {
            ops = TokMap.singleton Colon (term RParen (more_pi ()));
            name = Some (Lazy (lazy (explicit_pi_vars ())));
            term = None;
            fail = [];
          }
      and implicit_pi_vars () =
        Inner
          {
            ops =
              TokMap.singleton Colon
                (terms
                   [
                     (Coloneq, Flag (Default_pi, term RBrace (Lazy (lazy (more_pi ())))));
                     (RBrace, Lazy (lazy (more_pi ())));
                   ]);
            name = Some (Lazy (lazy (implicit_pi_vars ())));
            term = None;
            fail = [];
          }
      and more_pi () =
        ops
          [
            (LParen, Lazy (lazy (explicit_pi ())));
            (LBrace, Lazy (lazy (implicit_pi ())));
            (Arrow, Done n);
          ] in
      eops [ (LParen, explicit_pi ()); (LBrace, implicit_pi ()) ])

let rec compile_pi : type n. (string option, n) Bwv.t -> observation list -> n check option =
 fun ctx obs ->
  let f = get_flag [ Explicit_pi; Implicit_pi ] obs in
  match f with
  | Some Implicit_pi -> raise (Failure "Implicit pi-types not implemented")
  | Some Explicit_pi -> compile_pi_names Zero ctx obs
  | _ ->
      let body, obs = get_term obs in
      let () = get_done obs in
      compile ctx body

and compile_pi_names :
    type m n mn.
    (m, n, mn) N.plus -> (string option, mn) Bwv.t -> observation list -> m check option =
 fun mn ctx obs ->
  let x, obs = get_next obs in
  match x with
  | `Done -> raise (Failure "Unexpected end of arguments")
  | `Name x -> compile_pi_names (Suc mn) (Snoc (ctx, x)) obs
  | `Term dom -> (
      let f = get_flag [ Default_pi ] obs in
      match f with
      | Some Default_pi -> raise (Failure "Default arguments not implemented")
      | _ ->
          let* cod = compile_pi ctx obs in
          compile_pi_doms mn ctx dom cod)

and compile_pi_doms :
    type m n mn.
    (m, n, mn) N.plus -> (string option, mn) Bwv.t -> result -> mn check -> m check option =
 fun mn ctx dom cod ->
  match (mn, ctx) with
  | Zero, _ -> return cod
  | Suc mn, Snoc (ctx, _) ->
      let* cdom = compile ctx dom in
      compile_pi_doms mn ctx dom (Synth (Pi (cdom, cod)))

let () = add_compiler pi { compile = compile_pi }

let asc =
  make ~name:":" ~tightness:Float.neg_infinity ~left:Open ~right:Open ~assoc:Non ~tree:(fun n ->
      eop Colon (Done n))

let () =
  add_compiler asc
    {
      compile =
        (fun ctx obs ->
          let tm, obs = get_term obs in
          let ty, obs = get_term obs in
          let () = get_done obs in
          let* tm = compile ctx tm in
          let* ty = compile ctx ty in
          return (Synth (Asc (tm, ty))));
    }

let arrow =
  make ~name:"->" ~tightness:0. ~left:Open ~right:Open ~assoc:Right ~tree:(fun n ->
      eop Arrow (Done n))

let () =
  add_compiler arrow
    {
      compile =
        (fun ctx obs ->
          let tm, obs = get_term obs in
          let ty, obs = get_term obs in
          let () = get_done obs in
          let* tm = compile ctx tm in
          let* ty = compile (Snoc (ctx, None)) ty in
          return (Synth (Pi (tm, ty))));
    }

let universe =
  make ~name:"Type" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop (Name "Type") (Done n))

let () =
  add_compiler universe
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          return (Synth (Symbol (UU, Zero, Emp))));
    }

let refl =
  make ~name:"refl" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop (Name "refl") (Done n))

let () =
  add_compiler refl
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          return (Synth (Symbol (Refl, Suc Zero, Emp))));
    }

let sym =
  make ~name:"sym" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop (Name "sym") (Done n))

let () =
  add_compiler sym
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          return (Synth (Symbol (Sym, Suc Zero, Emp))));
    }

let id =
  make ~name:"Id" ~tightness:Float.nan ~left:Closed ~right:Closed ~assoc:Non ~tree:(fun n ->
      eop (Name "Id") (Done n))

let () =
  add_compiler id
    {
      compile =
        (fun _ obs ->
          let () = get_done obs in
          return (Synth (Symbol (Id, Suc (Suc (Suc Zero)), Emp))));
    }

let builtins =
  ref
    (State.empty
    |> State.add parens
    |> State.add letin
    |> State.add pi
    |> State.add asc
    |> State.add arrow
    |> State.add universe
    |> State.add refl
    |> State.add sym
    |> State.add id)
