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
  | PVal : ('mode, 'a, 'b) Ctx.t * ('mode, kinetic) value -> printable
  | PNormal : ('mode, 'a, 'b) Ctx.t * 'mode normal -> printable
  | (* When printing a hole we use a termctx, since that's what we store anyway, and we would also have to read back a value context anyway in order to unparse it. *)
      PHole :
      Origin.t * (string option, 'a) Bwv.t * ('mode, 'a, 'b) termctx * ('mode, 'b, kinetic) term
      -> printable
