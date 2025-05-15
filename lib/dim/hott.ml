open Util
open Singleton
open Deg
open Sface
open Cube
open Tube

type dim = D.one

let dim : dim D.t = D.one
let singleton : dim is_singleton = One

let sym : type b. (dim, dim, b) D.plus -> (b, b) deg =
 fun (Suc Zero) -> Suc (Suc (Zero D.zero, Now), Later Now)

let faces : unit -> ((D.zero, dim) sface * (D.zero, dim) sface * N.two Endpoints.len) option =
 fun () ->
  Option.map
    (fun two -> (End (Zero, (two, Pop Top)), End (Zero, (two, Top)), two))
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

let cube2 : type a b.
    (dim, dim, b) D.plus -> a -> a -> a -> a -> a -> a -> a -> a -> a -> (b, a) CubeOf.t option =
 fun (Suc Zero) x00 x01 x02 x10 x11 x12 x20 x21 x22 ->
  Option.map
    (fun two ->
      CubeOf.Branch
        ( two,
          Snoc
            ( Snoc (Emp, Branch (two, Snoc (Snoc (Emp, Leaf x00), Leaf x01), Leaf x02)),
              Branch (two, Snoc (Snoc (Emp, Leaf x10), Leaf x11), Leaf x12) ),
          Branch (two, Snoc (Snoc (Emp, Leaf x20), Leaf x21), Leaf x22) ))
    (Endpoints.hott ())

let tube12 : type a b.
    (dim, dim, b) D.plus -> a -> a -> a -> a -> a -> a -> (dim, dim, b, a) TubeOf.t option =
 fun (Suc Zero) x00 x01 x02 x10 x11 x12 ->
  Option.map
    (fun two ->
      TubeOf.Branch
        ( two,
          Snoc
            ( Snoc (Emp, Branch (two, Snoc (Snoc (Emp, Leaf x00), Leaf x01), Leaf x02)),
              Branch (two, Snoc (Snoc (Emp, Leaf x10), Leaf x11), Leaf x12) ),
          Leaf dim ))
    (Endpoints.hott ())
