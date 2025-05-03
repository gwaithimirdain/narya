open Bwd
open Bwd.Infix
open Dim
open Util
open Perhaps
open Term
open Monad.Ops (Monad.Maybe)

let ([ ftrr; fliftr; ftrl; fliftl; fid ] : (Hott.dim Field.t, Fwn.five) Vec.t) =
  Vec.map (fun x -> Field.intern x Hott.dim) [ "trr"; "liftr"; "trl"; "liftl"; "id" ]

let fields : (Tbwd.emp * D.zero * no_eta) CodatafieldAbwd.t option Lazy.t =
  lazy
    (let* zero, one, two = Hott.faces () in
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
       <: Entry (ftrr, Higher (plusmap, trr))
       <: Entry (fliftr, Higher (plusmap, liftr))
       <: Entry (ftrl, Higher (plusmap, trl))
       <: Entry (fliftl, Higher (plusmap, liftl))))

(* The dimension 'n of the Structfields is alost always 0, since it is the substitution dimension of the type being checked against, and canonical types are almost always defined to belong to the 0-dimensional universe.  The one exception, of course, is Gel/glue, where this is the gel dimension.  *)

(* These are lazy only to delay them until we're inside Dim.Endpoints.run. *)

type pi_ctx = ((Tbwd.emp, D.zero) Tbwd.snoc, D.zero) Tbwd.snoc

let pi :
    (D.zero * ((Tbwd.emp, D.zero) Tbwd.snoc, D.zero) Tbwd.snoc * potential * no_eta * some)
    StructfieldAbwd.t
    option
    Lazy.t =
  lazy
    (let plusmap =
       Plusmap.Map_snoc (Map_snoc (Map_emp, D.plus_zero Hott.dim), D.plus_zero Hott.dim) in
     let plusfam x = Some (PlusFam.PlusFam (plusmap, x)) in
     let fname = singleton_variables D.zero (Some "f") in
     let xname = singleton_variables D.zero (Some "x") in
     let module Context = struct
       type t =
         ( (((Tbwd.emp, Hott.dim) Tbwd.snoc, Hott.dim) Tbwd.snoc, D.zero) Tbwd.snoc,
           D.zero )
         Tbwd.snoc
     end in
     let a2 : (Context.t, kinetic) term =
       Var (Index (Later (Later (Later Now)), id_sface Hott.dim)) in
     let b2 : (Context.t, kinetic) term = Var (Index (Later (Later Now), id_sface Hott.dim)) in
     let f : (Context.t, kinetic) term = Var (Index (Later Now, id_sface D.zero)) in
     let x : (Context.t, kinetic) term = Var (Index (Now, id_sface D.zero)) in
     let trl_x = app (Field (a2, ftrl, zero_ins Hott.dim)) x in
     let liftl_x = app (Field (a2, fliftl, zero_ins Hott.dim)) x in
     let* lxcube = Hott.cube trl_x x liftl_x in
     let trr_x = app (Field (a2, ftrr, zero_ins Hott.dim)) x in
     let liftr_x = app (Field (a2, fliftr, zero_ins Hott.dim)) x in
     let* rxcube = Hott.cube x trr_x liftr_x in
     let trr : type r. (D.zero, Hott.dim, r) pbij -> (r, pi_ctx) PlusFam.t =
      fun p ->
       let Eq = eq_of_zero_pbij p in
       plusfam
         (Lam
            ( fname,
              Lam
                ( xname,
                  Realize (app (Field (App (b2, lxcube), ftrr, zero_ins Hott.dim)) (app f trl_x)) )
            )) in
     let trr = PlusPbijmap.build D.zero Hott.dim { build = trr } in
     let trl : type r. (D.zero, Hott.dim, r) pbij -> (r, pi_ctx) PlusFam.t =
      fun p ->
       let Eq = eq_of_zero_pbij p in
       plusfam
         (Lam
            ( fname,
              Lam
                ( xname,
                  Realize (app (Field (App (b2, rxcube), ftrl, zero_ins Hott.dim)) (app f trr_x)) )
            )) in
     let trl = PlusPbijmap.build D.zero Hott.dim { build = trl } in
     (* I haven't written out liftr and liftl yet. *)
     (* let id : type r. (D.zero, Hott.dim, r) pbij -> (r, pi_ctx) PlusFam.t =
         fun p ->
          let Eq = eq_of_zero_pbij p in
          Reporter.fatal (Unimplemented "pi.id") in
        let id = PlusPbijmap.build D.zero Hott.dim { build = id } in *)
     return
       (Emp
       <: StructfieldAbwd.Entry (ftrr, Higher trr)
       (* <: Entry (fliftr, Higher liftr) *)
       <: Entry (ftrl, Higher trl)
          (* <: Entry (fliftl, Higher liftl) *)
          (* <: Entry (fid, Higher id) *)))

let universe : (D.zero * Tbwd.emp * potential * no_eta * some) StructfieldAbwd.t option Lazy.t =
  Lazy.from_val None

let codata : type a n et.
    (a * n * et) CodatafieldAbwd.t ->
    (n * a * potential * no_eta * some) StructfieldAbwd.t option Lazy.t =
 fun _ -> Lazy.from_val None

let data : unit option Lazy.t = Lazy.from_val None
