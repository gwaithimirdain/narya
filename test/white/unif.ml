open Dim
open Modal
open Core
open Term
open Value
open Testutil.Mcp
open Testutil.Testmode

(* Blocked evaluation of a case tree stuck on a unification metavariable.  There is no unification yet, so we create and solve a unification metavariable directly. *)

(* What forcing the value of a neutral produces, and what is then cached in it. *)
let forced (v : (test_mode, kinetic) value) : string =
  match v with
  | Neu { value; _ } -> (
      match Norm.force_eval value with
      | Blocked _ -> "blocked"
      | Unrealized -> "unrealized"
      | Realize _ -> "realized"
      | Val _ -> "val")
  | _ -> "not neutral"

let cached (v : (test_mode, kinetic) value) : string =
  match v with
  | Neu { value; _ } -> (
      match !value with
      | Ready _ -> "ready"
      | Blocked_on _ -> "blocked_on"
      | _ -> "unforced")
  | _ -> "not neutral"

let expect what got expected =
  if got <> expected then
    raise (Failure (Printf.sprintf "%s: expected %s, got %s" what expected got))

let () =
  run @@ fun () ->
  Testutil.Repl.def "Bool" "Type" "data [ true. | false. ]";
  Testutil.Repl.def "ℕ" "Type" "data [ zero. | suc. (_ : ℕ) ]";
  Testutil.Repl.def "T" "Bool → Type" "b ↦ match b [ true. ↦ ℕ | false. ↦ Bool ]";
  let boolty, _ = synth "Bool" in
  let tfam, _ = synth "T" in
  Global.run @@ fun () ->
  let ctx = Ctx.empty test_mode in
  match Check.make_unif ctx boolty with
  | Meta (meta, Unif_meta cell, Kinetic) as utm ->
      let u = Norm.eval_term (Ctx.env ctx) utm in
      expect "unsolved metavariable" (forced u) "blocked";
      (* T ?u is stuck on ?u, so its value is blocked, and cached with the computation that produced it. *)
      let tu =
        Norm.apply_term tfam (Modality.filter_zero (Modality.id test_mode)) (CubeOf.singleton u)
      in
      expect "T ?u before solving" (forced tu) "blocked";
      expect "T ?u cached before solving" (cached tu) "blocked_on";
      (* Solving ?u in the table of the current command unblocks T ?u, but since that solution could still be backtracked, the result isn't cached. *)
      let truetm = Check.check Kinetic ctx (parse_term Emp "true.") boolty in
      Global.solve_unif meta truetm;
      expect "T ?u after speculative solution" (forced tu) "realized";
      expect "T ?u cached after speculative solution" (cached tu) "blocked_on";
      (* Once the solution is written into the cell, as happens when a command succeeds, the result is cached. *)
      cell := Some truetm;
      expect "T ?u after permanent solution" (forced tu) "realized";
      expect "T ?u cached after permanent solution" (cached tu) "ready";
      (* And T ?u now unfolds to ℕ. *)
      Testutil.Mcp.equal_at tu (fst (synth "ℕ")) (fst (synth "Type"));
      (* A speculation can only solve the unification metavariables created inside it, including after it has succeeded into the enclosing computation. *)
      let assignable (tm : (test_mode, test_mode Tctx.emp, kinetic) term) =
        match tm with
        | Meta (meta, Unif_meta _, Kinetic) -> Global.unif_assignable meta
        | _ -> raise (Failure "not a unification metavariable") in
      let outer = Check.make_unif ctx boolty in
      let speculate f =
        match Origin.Origin.speculate (fun () -> Ok (f ())) with
        | Ok x -> x
        | Error () -> raise (Failure "speculation failed") in
      expect "outer at top level" (string_of_bool (assignable outer)) "true";
      let inner =
        speculate @@ fun () ->
        expect "outer inside speculation" (string_of_bool (assignable outer)) "false";
        let inner = Check.make_unif ctx boolty in
        expect "inner inside speculation" (string_of_bool (assignable inner)) "true";
        inner in
      expect "inner after success" (string_of_bool (assignable inner)) "true";
      speculate (fun () ->
          expect "inner inside later speculation" (string_of_bool (assignable inner)) "false")
  | _ -> raise (Failure "make_unif didn't make a unification metavariable")
