open Term
open Value
open Status
open Reporter

type 'a located = 'a Asai.Range.located

val ty : ('mode, 'a, 'b) Ctx.t -> ('mode, kinetic) value -> unit
val tm : ('mode, 'a, 'b) Ctx.t -> ('b, 's) term -> unit
val ctx : ('mode, 'b, 's) status -> ('mode, 'a, 'b) Ctx.t -> 'a Raw.check located -> unit

type ctx_handler = {
  handle : 'mode 'a 'b 's. ('mode, 'b, 's) status -> ('mode, 'a, 'b) Ctx.t -> 'a Raw.check located -> unit;
}

type tm_handler = printable located -> unit
type ty_handler = printable located -> unit

val run : ?ctx:ctx_handler -> ?tm:tm_handler -> ?ty:ty_handler -> (unit -> 'a) -> 'a
