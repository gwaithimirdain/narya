(* This module should not be opened, but used qualified. *)
open Status
open Reporter
open Printable

type 'a located = 'a Asai.Range.located

let locate_opt = Asai.Range.locate_opt

type _ Effect.t +=
  | Ty : printable located -> unit Effect.t
  | Tm : printable located -> unit Effect.t
  | Ctx : (('mode, 'b, 's) status * ('mode, 'a, 'b) Ctx.t * 'a Raw.check located) -> unit Effect.t

(* Annotations are requested at every term that is synthesized or checked, but usually nobody is listening for them.  Performing an effect costs time proportional to the number of handlers installed between the "perform" and its handler, which for these effects includes all the handlers installed by every enclosing "import" of a file being loaded from source.  So we record whether any nontrivial handler is installed, and if not we don't perform the effects (or even construct their arguments). *)
let listening = ref false
let ty ctx v = if !listening then Effect.perform (Ty (locate_opt (get_loc ()) (PVal (ctx, v))))
let tm ctx x = if !listening then Effect.perform (Tm (locate_opt (get_loc ()) (PTerm (ctx, x))))
let ctx status ctx tm = if !listening then Effect.perform (Ctx (status, ctx, tm))

open Effect.Deep

type ctx_handler = {
  handle :
    'mode 'a 'b 's. ('mode, 'b, 's) status -> ('mode, 'a, 'b) Ctx.t -> 'a Raw.check located -> unit;
}

type tm_handler = printable located -> unit
type ty_handler = printable located -> unit

let trivial_ctx_handler : ctx_handler = { handle = (fun _ _ _ -> ()) }

let run (type a) ?ctx ?tm ?ty (f : unit -> a) =
  let old = !listening in
  listening := old || Option.is_some ctx || Option.is_some tm || Option.is_some ty;
  Fun.protect ~finally:(fun () -> listening := old) @@ fun () ->
  let ctx = Option.value ctx ~default:trivial_ctx_handler in
  let tm = Option.value tm ~default:(fun _ -> ()) in
  let ty = Option.value ty ~default:(fun _ -> ()) in
  try f () with
  | effect Tm p, k ->
      tm p;
      continue k ()
  | effect Ty p, k ->
      ty p;
      continue k ()
  | effect Ctx (s, c, tm), k ->
      ctx.handle s c tm;
      continue k ()
