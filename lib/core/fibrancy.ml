open Bwd
open Bwd.Infix
open Dim
open Util
open Term
open Monad.Ops (Monad.Maybe)

let fields : unit -> (Tbwd.emp * D.zero * no_eta) CodatafieldAbwd.t option =
 fun () ->
  let* zero, one, two = Hott.faces () in
  let plusmap = Plusmap.Map_snoc (Map_emp, D.plus_zero Hott.dim) in
  let open CodatafieldAbwd in
  let trr =
    Pi
      ( None,
        CubeOf.singleton (Var (Index (Now, one))),
        CodCube.singleton (Var (Index (Later Now, zero))) ) in
  let liftr =
    Pi
      ( Some "x₀",
        CubeOf.singleton (Var (Index (Now, one))),
        CodCube.singleton
          (Inst
             ( Var (Index (Later Now, id_sface Hott.dim)),
               TubeOf.of_cube_bwv D.zero Hott.singleton (D.zero_plus Hott.dim) two
                 (Snoc
                    ( Snoc (Emp, CubeOf.singleton (Var (Index (Now, id_sface D.zero)))),
                      CubeOf.singleton
                        (App
                           ( Field
                               ( Var (Index (Later Now, id_sface Hott.dim)),
                                 Field.intern "trr" Hott.dim,
                                 id_ins D.zero (D.zero_plus Hott.dim) ),
                             CubeOf.singleton (Var (Index (Now, id_sface D.zero))) )) )) )) ) in
  let trl =
    Pi
      ( None,
        CubeOf.singleton (Var (Index (Now, zero))),
        CodCube.singleton (Var (Index (Later Now, one))) ) in
  let liftl =
    Pi
      ( Some "x₁",
        CubeOf.singleton (Var (Index (Now, zero))),
        CodCube.singleton
          (Inst
             ( Var (Index (Later Now, id_sface Hott.dim)),
               TubeOf.of_cube_bwv D.zero Hott.singleton (D.zero_plus Hott.dim) two
                 (Snoc
                    ( Snoc
                        ( Emp,
                          CubeOf.singleton
                            (App
                               ( Field
                                   ( Var (Index (Later Now, id_sface Hott.dim)),
                                     Field.intern "trl" Hott.dim,
                                     id_ins D.zero (D.zero_plus Hott.dim) ),
                                 CubeOf.singleton (Var (Index (Now, id_sface D.zero))) )) ),
                      CubeOf.singleton (Var (Index (Now, id_sface D.zero))) )) )) ) in
  return
    (Emp
    <: Entry (Field.intern "trr" Hott.dim, Higher (plusmap, trr))
    <: Entry (Field.intern "liftr" Hott.dim, Higher (plusmap, liftr))
    <: Entry (Field.intern "trl" Hott.dim, Higher (plusmap, trl))
    <: Entry (Field.intern "liftl" Hott.dim, Higher (plusmap, liftl)))
