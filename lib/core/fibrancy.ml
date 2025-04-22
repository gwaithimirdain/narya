open Bwd
open Bwd.Infix
open Dim
open Util
open Term

let fields : (Tbwd.emp * D.zero * no_eta) CodatafieldAbwd.t option ref = ref None

let install (dim : Dim.hott_direction option) =
  match dim with
  | None -> ()
  | Some (Hott (dim, sdim, zero, one, two)) ->
      let plusmap = Plusmap.Map_snoc (Map_emp, D.plus_zero dim) in
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
                 ( Var (Index (Later Now, id_sface dim)),
                   TubeOf.of_cube_bwv D.zero sdim (D.zero_plus dim) two
                     (Snoc
                        ( Snoc (Emp, CubeOf.singleton (Var (Index (Now, id_sface D.zero)))),
                          CubeOf.singleton
                            (App
                               ( Field
                                   ( Var (Index (Later Now, id_sface dim)),
                                     Field.intern "trr" dim,
                                     id_ins D.zero (D.zero_plus dim) ),
                                 CubeOf.singleton (Var (Index (Now, id_sface D.zero))) )) )) )) )
      in
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
                 ( Var (Index (Later Now, id_sface dim)),
                   TubeOf.of_cube_bwv D.zero sdim (D.zero_plus dim) two
                     (Snoc
                        ( Snoc
                            ( Emp,
                              CubeOf.singleton
                                (App
                                   ( Field
                                       ( Var (Index (Later Now, id_sface dim)),
                                         Field.intern "trl" dim,
                                         id_ins D.zero (D.zero_plus dim) ),
                                     CubeOf.singleton (Var (Index (Now, id_sface D.zero))) )) ),
                          CubeOf.singleton (Var (Index (Now, id_sface D.zero))) )) )) ) in
      fields :=
        Some
          (Emp
          <: Entry (Field.intern "trr" dim, Higher (plusmap, trr))
          <: Entry (Field.intern "liftr" dim, Higher (plusmap, liftr))
          <: Entry (Field.intern "trl" dim, Higher (plusmap, trl))
          <: Entry (Field.intern "liftl" dim, Higher (plusmap, liftl)))
