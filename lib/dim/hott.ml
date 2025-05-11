open Util
open Singleton
open Sface
open Cube
open Tube

type dim = D.one

let dim : dim D.t = D.one
let singleton : dim is_singleton = One

let faces : unit -> ((D.zero, dim) sface * (D.zero, dim) sface * N.two Endpoints.len) option =
 fun () ->
  Option.map
    (fun two -> (End (Zero, (two, Top)), End (Zero, (two, Pop Top)), two))
    (Endpoints.hott ())

let cube : type a. a -> a -> a -> (dim, a) CubeOf.t option =
 fun x0 x1 x2 ->
  Option.map
    (fun two -> CubeOf.Branch (two, Snoc (Snoc (Emp, Leaf x0), Leaf x1), Leaf x2))
    (Endpoints.hott ())

let tube : type a. a -> a -> (D.zero, dim, dim, a) TubeOf.t option =
 fun x0 x1 ->
  Option.map
    (fun two -> TubeOf.Branch (two, Snoc (Snoc (Emp, Leaf x0), Leaf x1), Leaf D.zero))
    (Endpoints.hott ())
