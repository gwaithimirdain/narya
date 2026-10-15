open Util
open Modal
open Core
open Parser
open Value
open Norm
open Asai.Range
open Testmode

(* The current context of assumptions, including names. *)
type ctx = Ctx : (test_mode, 'n, 'b) Ctx.t * (string option, 'n) Bwv.t -> ctx

let ectx = Ctx (Ctx.empty test_mode, Emp)
let context = ref ectx

(* Functions to synth and check terms *)

let parse_term names (tm : string) =
  let p = Parse.Term.parse (`String { content = tm; title = Some "user-supplied term" }) in
  let (Wrap tm) = Parse.Term.final p in
  Postprocess.process names tm

let synth (tm : string) : (test_mode, kinetic) value * (test_mode, kinetic) value =
  let (Ctx (ctx, names)) = !context in
  Reporter.run ~emit:Reporter.display ~fatal:(fun d ->
      Reporter.display_bwd d;
      raise (Failure "Failed to synthesize"))
  @@ fun () ->
  match parse_term names tm with
  | { value = Synth raw; loc } ->
      let syn, ty = Check.synth (Kinetic `Nolet) ctx { value = raw; loc } in
      let esyn = eval_term (Ctx.env ctx) syn in
      (esyn, ty)
  | _ -> Reporter.fatal (Nonsynthesizing "toplevel synth")

let check (tm : string) (ty : (test_mode, kinetic) value) : (test_mode, kinetic) value =
  let (Ctx (ctx, names)) = !context in
  Reporter.run ~emit:Reporter.display ~fatal:(fun d ->
      Reporter.display_bwd d;
      raise (Failure "Failed to check"))
  @@ fun () -> eval_term (Ctx.env ctx) (Check.check (Kinetic `Nolet) ctx (parse_term names tm) ty)

(* Assert that a term *doesn't* synthesize or check, and possibly ensure it gives a specific error code.  We check the first error reported, whether it is fatal or mortal. *)

let expect_error ?print ?code ?short (success : string) (f : unit -> unit) : unit =
  let errs =
    match Reporter.collect f with
    | Ok (), errs -> errs
    | Error d, errs -> Snoc (errs, d) in
  match Bwd_extra.to_list_map Fun.id errs with
  | [] -> raise (Failure success)
  | d :: _ ->
      let ok =
        match (code, short) with
        | Some c, _ -> d.message = c
        | None, Some str -> Reporter.Code.short_code d.message = str
        | None, None -> true in
      if ok then (if Option.is_some print then Reporter.display d)
      else (
        Reporter.display d;
        raise (Failure "Unexpected error code"))

let unsynth : ?print:unit -> ?code:Reporter.Code.t -> ?short:string -> string -> unit =
 fun ?print ?code ?short tm ->
  let (Ctx (ctx, names)) = !context in
  expect_error ?print ?code ?short "Synthesis success" @@ fun () ->
  match parse_term names tm with
  | { value = Synth raw; loc } -> ignore (Check.synth (Kinetic `Nolet) ctx { value = raw; loc })
  | _ -> Reporter.fatal (Nonsynthesizing "top-level unsynth")

let uncheck :
    ?print:unit ->
    ?code:Reporter.Code.t ->
    ?short:string ->
    string ->
    (test_mode, kinetic) value ->
    unit =
 fun ?print ?code ?short tm ty ->
  let (Ctx (ctx, names)) = !context in
  expect_error ?print ?code ?short "Checking success" @@ fun () ->
  ignore (Check.check (Kinetic `Nolet) ctx (parse_term names tm) ty)

(* Assert that a term doesn't parse *)

let unparse : ?print:unit -> string -> unit =
 fun ?print tm ->
  let (Ctx (_, names)) = !context in
  Reporter.try_with
    ~fatal:(fun d -> if Option.is_some print then Reporter.display d)
    (fun () ->
      let _ = parse_term names tm in
      raise (Failure "Unexpected parse success"))

(* Add to the context of assumptions *)

let assume (x : string) (ty : (test_mode, kinetic) value) : (test_mode, kinetic) value =
  let (Ctx (ctx, names)) = !context in
  context := Ctx (Ctx.ext ctx (Modality.id test_mode) (Some x) ty, Bwv.snoc names (Some x));
  fst (synth x)

(* Check that two terms are, or aren't, equal, at a type or synthesizing *)

let equal_at (tm1 : (test_mode, kinetic) value) (tm2 : (test_mode, kinetic) value)
    (ty : (test_mode, kinetic) value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Result.is_ok (Equal.equal_at ctx tm1 tm2 ty) then () else raise (Failure "Unequal terms")

let unequal_at (tm1 : (test_mode, kinetic) value) (tm2 : (test_mode, kinetic) value)
    (ty : (test_mode, kinetic) value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Result.is_error (Equal.equal_at ctx tm1 tm2 ty) then () else raise (Failure "Equal terms")

let equal (tm1 : (test_mode, kinetic) value) (tm2 : (test_mode, kinetic) value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Result.is_ok (Equal.equal_val ctx tm1 tm2) then () else raise (Failure "Unequal terms")

let unequal (tm1 : (test_mode, kinetic) value) (tm2 : (test_mode, kinetic) value) : unit =
  let (Ctx (ctx, _)) = !context in
  if Result.is_error (Equal.equal_val ctx tm1 tm2) then () else raise (Failure "Equal terms")

let run f = Repl.run f
