open Dim
open Term

let dim : D.wrapped option ref = ref None
let install d = dim := Some d

let fields : type a b. (a, b) Ctx.t -> (b * D.zero * no_eta) CodatafieldAbwd.t option =
 fun _ctx ->
  match !dim with
  | None -> None
  | Some _dim -> Reporter.(fatal (Unimplemented "fibrancy"))
