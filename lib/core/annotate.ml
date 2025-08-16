(* This module should not be opened, but used qualified. *)
open Status
open Reporter
open Printable

type 'a located = 'a Asai.Range.located

let locate_opt = Asai.Range.locate_opt

type _ Effect.t +=
  | Ty : printable located -> unit Effect.t
  | Tm : printable located -> unit Effect.t
  | Ctx : (('b, 's) status * ('a, 'b) Ctx.t * 'a Raw.check located) -> unit Effect.t

let ty ctx v = Effect.perform (Ty (locate_opt (get_loc ()) (PVal (ctx, v))))
let tm ctx x = Effect.perform (Tm (locate_opt (get_loc ()) (PTerm (ctx, x))))
let ctx status ctx tm = Effect.perform (Ctx (status, ctx, tm))

open Effect.Deep

type ctx_handler = {
  handle : 'a 'b 's. ('b, 's) status -> ('a, 'b) Ctx.t -> 'a Raw.check located -> unit;
}

type tm_handler = printable located -> unit
type ty_handler = printable located -> unit

let trivial_ctx_handler : ctx_handler = { handle = (fun _ _ _ -> ()) }

let run (type a) ?(ctx = trivial_ctx_handler) ?(tm = fun _ -> ()) ?(ty = fun _ -> ())
    (f : unit -> a) =
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
