open Util
open Term
open Value
open Reporter
open Origin

let phead : 'mode head -> printable = function
  | Const { name; _ } -> PConstant name
  | Meta { meta; _ } -> PMeta meta
  | _ -> PString "(variable)"

type printable +=
  | PLevel : level -> printable
  | PTerm : ('mode, 'a, 'b) Ctx.t * ('mode, 'b, 's) term -> printable
  | (* A head, read back only if it is printed.  Reading back a head can be expensive, e.g. for a metavariable with a nontrivial environment, and an equality check records the heads it finds unequal in case it has to report them, but usually doesn't. *)
      PHead :
      ('mode, 'a, 'b) Ctx.t * 'mode head
      -> printable
  | PVal : ('mode, 'a, 'b) Ctx.t * ('mode, kinetic) value -> printable
  | PNormal : ('mode, 'a, 'b) Ctx.t * 'mode normal -> printable
  | (* A printable whose values are printed normalized, even though values are usually printed folded (see Reporter.folded_printing). *)
      PNormalized :
      printable
      -> printable
  | (* When printing a hole we use a termctx, since that's what we store anyway, and we would also have to read back a value context anyway in order to unparse it. *)
      PHole :
      Origin.t * (string option, 'a) Bwv.t * ('mode, 'a, 'b) termctx * ('mode, 'b, kinetic) term
      -> printable
