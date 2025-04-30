open Util
open Singleton
open Sface

type dim = D.one

let dim : dim D.t = D.one
let singleton : dim is_singleton = One

let faces : unit -> ((D.zero, dim) sface * (D.zero, dim) sface * N.two Endpoints.len) option =
 fun () ->
  Option.map
    (fun two -> (End (Zero, (two, Top)), End (Zero, (two, Pop Top)), two))
    (Endpoints.hott ())
