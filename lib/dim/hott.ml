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
 fun (Suc (Zero, Unit)) -> Suc (Suc (Zero D.zero, D.deg, Now), D.deg, Later Now)

let faces : unit -> ((D.zero, dim) sface * (D.zero, dim) sface * N.two Endpoints.len) option =
 fun () ->
  Option.map
    (fun two -> (End (Zero, D.deg, (two, Pop Top)), End (Zero, D.deg, (two, Top)), two))
    (Endpoints.hott ())

(* In these hand-built cubes, each leaf carries the bplus realizing its forwards decided word: a leaf reached after [d] Mid steps has decided word [cons deg (... nil)] ([d] times), realized by [Append_cons] applied [d] times to [Append_nil]. *)

let cube : type a. a -> a -> a -> (dim, a) CubeOf.t option =
 fun x0 x1 x2 ->
  Option.map
    (fun two ->
      CubeOf.Branch
        ( D.deg,
          two,
          Snoc (Snoc (Emp, Leaf (Append_nil, x0)), Leaf (Append_nil, x1)),
          Leaf (Append_cons Append_nil, x2) ))
    (Endpoints.hott ())

let tube : type a. a -> a -> (D.zero, dim, dim, a) TubeOf.t option =
 fun x0 x1 ->
  Option.map
    (fun two ->
      TubeOf.Branch
        (D.deg, two, Snoc (Snoc (Emp, Leaf (Append_nil, x0)), Leaf (Append_nil, x1)), Leaf D.zero))
    (Endpoints.hott ())

let cube2 : type a b.
    (dim, dim, b) D.plus -> a -> a -> a -> a -> a -> a -> a -> a -> a -> (b, a) CubeOf.t option =
 fun (Suc (Zero, Unit)) x00 x01 x02 x10 x11 x12 x20 x21 x22 ->
  Option.map
    (fun two ->
      CubeOf.Branch
        ( D.deg,
          two,
          Snoc
            ( Snoc
                ( Emp,
                  Branch
                    ( D.deg,
                      two,
                      Snoc (Snoc (Emp, Leaf (Append_nil, x00)), Leaf (Append_nil, x01)),
                      Leaf (Append_cons Append_nil, x02) ) ),
              Branch
                ( D.deg,
                  two,
                  Snoc (Snoc (Emp, Leaf (Append_nil, x10)), Leaf (Append_nil, x11)),
                  Leaf (Append_cons Append_nil, x12) ) ),
          Branch
            ( D.deg,
              two,
              Snoc
                ( Snoc (Emp, Leaf (Append_cons Append_nil, x20)),
                  Leaf (Append_cons Append_nil, x21) ),
              Leaf (Append_cons (Append_cons Append_nil), x22) ) ))
    (Endpoints.hott ())

let tube12 : type a b.
    (dim, dim, b) D.plus -> a -> a -> a -> a -> a -> a -> (dim, dim, b, a) TubeOf.t option =
 fun (Suc (Zero, Unit)) x00 x01 x02 x10 x11 x12 ->
  Option.map
    (fun two ->
      TubeOf.Branch
        ( D.deg,
          two,
          Snoc
            ( Snoc
                ( Emp,
                  Branch
                    ( D.deg,
                      two,
                      Snoc (Snoc (Emp, Leaf (Append_nil, x00)), Leaf (Append_nil, x01)),
                      Leaf (Append_cons Append_nil, x02) ) ),
              Branch
                ( D.deg,
                  two,
                  Snoc (Snoc (Emp, Leaf (Append_nil, x10)), Leaf (Append_nil, x11)),
                  Leaf (Append_cons Append_nil, x12) ) ),
          Leaf dim ))
    (Endpoints.hott ())
