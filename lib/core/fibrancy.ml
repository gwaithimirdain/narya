open Bwd
open Bwd.Infix
open Dim
open Util
open Tbwd
open Term
open Monad.Ops (Monad.Maybe)

(* Fibrancy fields *)

(* The types of the (user-accessible, non-corecursive) fibrancy fields *)

let ([ ftrr; fliftr; ftrl; fliftl; fid ] : (Hott.dim Field.t, Fwn.five) Vec.t) =
  Vec.map (fun x -> Field.intern x Hott.dim) [ "trr"; "liftr"; "trl"; "liftl"; "id" ]

let fields : (emp * D.zero * no_eta) CodatafieldAbwd.t option Lazy.t =
  lazy
    (let* zero, one, two = Hott.faces () in
     let plusmap = Plusmap.Map_snoc (Map_emp, D.plus_zero Hott.dim) in
     let open CodatafieldAbwd in
     let trr =
       Pi
         ( None,
           CubeOf.singleton (Var (Index (Now, zero))),
           CodCube.singleton (Var (Index (Later Now, one))) ) in
     let liftr =
       Pi
         ( Some "x₀",
           CubeOf.singleton (Var (Index (Now, zero))),
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
           CubeOf.singleton (Var (Index (Now, one))),
           CodCube.singleton (Var (Index (Later Now, zero))) ) in
     let liftl =
       Pi
         ( Some "x₁",
           CubeOf.singleton (Var (Index (Now, one))),
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

(* Bisimulations and glue types (currently only 1-dimensional).  Will be defined later by parsing. *)

let glue = Constant.make Compunit.basic
let bisim = Constant.make Compunit.basic

(* Tube contexts *)

(* A witness of ('n, 'b) tube_ctx says that 'b is a term context of the form
     n, n, n-1, n-1, ..., 0, 0
   which is the context of iterated instantiations of an (n+1)-dimensional type.  We define these contexts by inductively defining the more general class of contexts of the form
     n, n, n-1, n-1, ..., k, k
*)

type ('n, 'b, 'k) gtube_ctx =
  | Zero : 'n D.t -> ('n, ((emp, 'n) snoc, 'n) snoc, 'n) gtube_ctx
  | Suc :
      ('n, 'b, 'k1) gtube_ctx * ('k, Hott.dim, 'k1) D.plus
      -> ('n, (('b, 'k) snoc, 'k) snoc, 'k) gtube_ctx

type ('n, 'b) tube_ctx = ('n, 'b, D.zero) gtube_ctx

let rec dim_tube_ctx : type n b k. (n, b, k) gtube_ctx -> n D.t = function
  | Zero n -> n
  | Suc (tube_ctx, _) -> dim_tube_ctx tube_ctx

let rec codim_tube_ctx : type n b k. (n, b, k) gtube_ctx -> k D.t = function
  | Zero n -> n
  | Suc (tube_ctx, nh) -> D.minus (codim_tube_ctx tube_ctx) nh

let rec ctx_tube_ctx : type n b k. (n, b, k) gtube_ctx -> b Plusmap.OfDom.t = function
  | Zero n -> Plusmap.OfDom.suc (Plusmap.OfDom.suc Plusmap.OfDom.zero n) n
  | Suc (tube_ctx, _) as input ->
      let k = codim_tube_ctx input in
      Plusmap.OfDom.suc (Plusmap.OfDom.suc (ctx_tube_ctx tube_ctx) k) k

(* Given a tube context of dimension n, we can add Hott.dim (h) on the left of everything and extend it by two more zeros to obtain a tube context of dimension h+n.  This is what we do in the corecursive "id" field. *)

let rec plusmap_gtube_ctx : type n hn b hb k hk.
    (Hott.dim, n, hn) D.plus ->
    (Hott.dim, b, hb) Plusmap.t ->
    (Hott.dim, k, hk) D.plus ->
    (n, b, k) gtube_ctx ->
    (hn, hb, hk) gtube_ctx =
 fun hn hb hk tube_ctx ->
  match tube_ctx with
  | Zero _n ->
      let Eq = D.plus_uniq hn hk in
      let (Map_snoc (Map_snoc (Map_emp, p1), p2)) = hb in
      let Eq, Eq = (D.plus_uniq hn p1, D.plus_uniq hn p2) in
      Zero (D.plus_out Hott.dim hn)
  | Suc (tube_ctx, kh) ->
      let h_bh = hb in
      let (Map_snoc (Map_snoc (hb, hk1), hk2)) = h_bh in
      let Eq, Eq = (D.plus_uniq hk hk1, D.plus_uniq hk hk2) in
      let (Plus h_kh) = D.plus (codim_tube_ctx tube_ctx) in
      let hk_h = D.plus_assocl hk kh h_kh in
      Suc (plusmap_gtube_ctx hn hb h_kh tube_ctx, hk_h)

let plusmap_tube_ctx : type n hn b hb.
    (Hott.dim, n, hn) D.plus ->
    (Hott.dim, b, hb) Plusmap.t ->
    (n, b) tube_ctx ->
    (hn, ((hb, D.zero) snoc, D.zero) snoc) tube_ctx =
 fun hn hb tube_ctx ->
  Suc (plusmap_gtube_ctx hn hb (D.plus_zero Hott.dim) tube_ctx, D.zero_plus Hott.dim)

(* Passing across isomorphisms *)

(* As in the internal proofs of fibrancy, we sometimes need to pass across a definitional isomorphism.  We implement this by simply applying a pair of function terms. *)

let rec fib_iso : type b.
    b Plusmap.OfDom.t ->
    (* fib is the known-to-be-fibrant *type* that we are isomorphic to.  Not its fibrancy fields!  If we worked directly with its fibrancy fields, they would be potential terms, and we wouldn't be able to apply them to things inside kinetic terms. *)
    fib:(b, kinetic) term ->
    (* to_fn is the function from that type *to* the type now being proven fibrant. *)
    to_fn:(b, kinetic) term ->
    (* fro_fn is the function *from* the type now being proven fibrant to the one known to be fibrant. *)
    fro_fn:(b, kinetic) term ->
    (* We only use this for zero-dimensional fibrancy. *)
    (D.zero * b * potential * no_eta) StructfieldAbwd.t option =
 fun b ~fib ~to_fn ~fro_fn ->
  let* zero, one, _two = Hott.faces () in
  let (Exists (type hb) ((hb, plusmap) : hb Plusmap.OfCod.t * (Hott.dim, b, hb) Plusmap.t)) =
    Plusmap.exists Hott.dim b in
  let plusfam x = Some (PlusFam.PlusFam (plusmap, x)) in
  let tr : type r. [ `Left | `Right ] -> (D.zero, Hott.dim, r) pbij -> (r, b) PlusFam.t =
   fun which p ->
    let in_face, out_face, ftr =
      match which with
      | `Right -> (zero, one, ftrr)
      | `Left -> (one, zero, ftrl) in
    let Eq = eq_of_zero_pbij p in
    let xname = singleton_variables D.zero (Some "x") in
    let x = Var (Index (Now, id_sface D.zero)) in
    let fro_x = app (Weaken (Shift (Hott.dim, plusmap, Unact (op_of_sface in_face, fro_fn)))) x in
    let fib2 = Weaken (Shift (Hott.dim, plusmap, fib)) in
    let tr_fro_x = app (Field (fib2, ftr, zero_ins Hott.dim)) fro_x in
    let to_tr_fro_x =
      app (Weaken (Shift (Hott.dim, plusmap, Unact (op_of_sface out_face, to_fn)))) tr_fro_x in
    plusfam (Lam (xname, Realize to_tr_fro_x)) in
  let trr = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> tr `Right p) } in
  let trl = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> tr `Left p) } in
  let lift : type r. [ `Left | `Right ] -> (D.zero, Hott.dim, r) pbij -> (r, b) PlusFam.t =
   fun which p ->
    let in_face, _out_face, ftr, flift, cube =
      match which with
      | `Right -> (zero, one, ftrr, fliftr, Hott.cube)
      | `Left -> (one, zero, ftrl, fliftl, fun x0 x1 x2 -> Hott.cube x1 x0 x2) in
    let Eq = eq_of_zero_pbij p in
    let xname = singleton_variables D.zero (Some "x") in
    let x = Var (Index (Now, id_sface D.zero)) in
    let fro_x = app (Weaken (Shift (Hott.dim, plusmap, Unact (op_of_sface in_face, fro_fn)))) x in
    let fib2 = Weaken (Shift (Hott.dim, plusmap, fib)) in
    let tr_fro_x = app (Field (fib2, ftr, zero_ins Hott.dim)) fro_x in
    let lift_fro_x = app (Field (fib2, flift, zero_ins Hott.dim)) fro_x in
    let* xcube = cube fro_x tr_fro_x lift_fro_x in
    let to_lift_fro_x = App (Weaken (Shift (Hott.dim, plusmap, to_fn)), xcube) in
    plusfam (Lam (xname, Realize to_lift_fro_x)) in
  let liftr = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> lift `Right p) } in
  let liftl = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> lift `Left p) } in
  let id : type r. (D.zero, Hott.dim, r) pbij -> (r, b) PlusFam.t =
   fun p ->
    let Eq = eq_of_zero_pbij p in
    let x0name = singleton_variables D.zero (Some "x0") in
    let x1name = singleton_variables D.zero (Some "x1") in
    let x2name = singleton_variables D.zero (Some "x2") in
    let x0 = Var (Index (Later Now, id_sface D.zero)) in
    let fro2 = Weaken (Weaken (Shift (Hott.dim, plusmap, fro_fn))) in
    let to2 = Weaken (Weaken (Weaken (Shift (Hott.dim, plusmap, to_fn)))) in
    let fro_x0 =
      app (Weaken (Weaken (Shift (Hott.dim, plusmap, Unact (op_of_sface zero, fro_fn))))) x0 in
    let x1 = Var (Index (Now, id_sface D.zero)) in
    let fro_x1 =
      app (Weaken (Weaken (Shift (Hott.dim, plusmap, Unact (op_of_sface one, fro_fn))))) x1 in
    let* fro_x01 = Hott.tube fro_x0 fro_x1 in
    let fib2 = Weaken (Weaken (Shift (Hott.dim, plusmap, fib))) in
    let x2 = Var (Index (Now, id_sface D.zero)) in
    let* fro_x012 = Hott.cube (Weaken fro_x0) (Weaken fro_x1) x2 in
    let* x012 = Hott.cube (Weaken x0) (Weaken x1) x2 in
    let hb00 = Plusmap.OfDom.suc (Plusmap.OfDom.suc hb D.zero) D.zero in
    let* fields =
      fib_iso hb00
        ~fib:(Inst (fib2, fro_x01))
        ~to_fn:(Lam (x2name, App (Weaken fro2, fro_x012)))
        ~fro_fn:(Lam (x2name, App (to2, x012))) in
    plusfam
      (Lam (x0name, Lam (x1name, Struct { dim = D.zero; eta = Noeta; energy = Potential; fields })))
  in
  let id = lazy (PlusPbijmap.build D.zero Hott.dim { build = id }) in
  return
    (Emp
    <: StructfieldAbwd.Entry (ftrr, Higher trr)
    <: Entry (fliftr, Higher liftr)
    <: Entry (ftrl, Higher trl)
    <: Entry (fliftl, Higher liftl)
    <: Entry (fid, LazyHigher id))

(* Computing the fibrancy fields on canonical type-formers *)

(* We compute these directly as terms.  This puts the onus on us to define them in a well-typed way, but we try our best to copy the definitions that can be given (and typechecked) internally using the higher coinductive isFibrant.

   The dimension 'n of these Structfields is almost always 0, since it is the substitution dimension of the type being checked against, and canonical types are almost always defined to belong to the 0-dimensional universe.  The one exception, of course, is Gel/glue, where this is the gel dimension.  When n=0, we are proving isFibrant; when n is larger we're proving "refl isFibrant" or some higher version of it.

   The outer laziness is only to delay them until we're inside Dim.Endpoints.run.  Eventually when the HOTT dimension is built-in and always present, that won't be necessary (but we will still need the LazyHigher wrapper around the 'id' field in some cases).  *)

(* Pi-types *)

(* In the case of pi-types, we could probably literally write the definitions in Narya, typecheck them, and insert them here.  However, we stick with defining the terms explicitly in code, for parallelism with the other fibrancy proofs where that is not possible. *)

let pi :
    (D.zero * ((emp, D.zero) snoc, D.zero) snoc * potential * no_eta) StructfieldAbwd.t option
    Lazy.t =
  lazy
    (let b = Plusmap.OfDom.suc (Plusmap.OfDom.suc Plusmap.OfDom.zero D.zero) D.zero in
     let dom = Var (Index (Later Now, id_sface D.zero)) in
     let cod = Var (Index (Now, id_sface D.zero)) in
     let* zero, one, _two = Hott.faces () in
     (* All the fields are 1-dimenional higher fields, where 1 denotes Hott.dim.  So we will be working in a context degenerated by this dimension, which we also denote 'h'. *)
     let (Exists
            (type hb)
            ((hb, plusmap) :
              hb Plusmap.OfCod.t * (Hott.dim, ((emp, D.zero) snoc, D.zero) snoc, hb) Plusmap.t)) =
       Plusmap.exists Hott.dim b in
     let plusfam x = Some (PlusFam.PlusFam (plusmap, x)) in
     (* Some arbitrarily chosen variable names *)
     let fname = singleton_variables D.zero (Some "f") in
     let xname = singleton_variables D.zero (Some "x") in
     (* The domain and codomain of our pi-type, shifted into the new context and thereby degenerated into 1-dimensional types, and weakened to lie in a context extended by the function being transported and its argument. *)
     let dom2 = Weaken (Weaken (Shift (Hott.dim, plusmap, dom))) in
     let dom0 = Weaken (Weaken (Shift (Hott.dim, plusmap, Unact (op_of_sface zero, dom)))) in
     let dom1 = Weaken (Weaken (Shift (Hott.dim, plusmap, Unact (op_of_sface one, dom)))) in
     let cod2 = Weaken (Weaken (Shift (Hott.dim, plusmap, cod))) in
     (* A generic function computing both trr and trl, which differ only in which operations they use and the order of boundaries. *)
     let tr : type r.
         [ `Left | `Right ] ->
         (D.zero, Hott.dim, r) pbij ->
         (r, ((emp, D.zero) snoc, D.zero) snoc) PlusFam.t =
      fun which p ->
       let ftr, funtr, funlift, cube =
         match which with
         | `Right -> (ftrr, ftrl, fliftl, Hott.cube)
         | `Left -> (ftrl, ftrr, fliftr, fun x0 x1 x2 -> Hott.cube x1 x0 x2) in
       let Eq = eq_of_zero_pbij p in
       (* The function argument that we'll be transporting *)
       let f : (((hb, D.zero) snoc, D.zero) snoc, kinetic) term =
         Var (Index (Later Now, id_sface D.zero)) in
       (* The argument of its transported version *)
       let x : (((hb, D.zero) snoc, D.zero) snoc, kinetic) term =
         Var (Index (Now, id_sface D.zero)) in
       let untr_x = app (Field (dom2, funtr, zero_ins Hott.dim)) x in
       let unlift_x = app (Field (dom2, funlift, zero_ins Hott.dim)) x in
       let* xcube = cube untr_x x unlift_x in
       let f_untr_x = app f untr_x in
       let tr_f_untr_x = app (Field (App (cod2, xcube), ftr, zero_ins Hott.dim)) f_untr_x in
       plusfam (Lam (fname, Lam (xname, Realize tr_f_untr_x))) in
     let trr = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> tr `Right p) } in
     let trl = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> tr `Left p) } in
     let xsname = singleton_variables Hott.dim (Some "x") in
     let refl = deg_zero Hott.dim in
     let (Plus hh) = D.plus Hott.dim in
     let sym = Hott.sym hh in
     (* Similarly, a generic function computing both liftl and liftr.  *)
     let lift : type r.
         [ `Left | `Right ] ->
         (D.zero, Hott.dim, r) pbij ->
         (r, ((emp, D.zero) snoc, D.zero) snoc) PlusFam.t =
      fun which p ->
       let zero, one, ftr, flift, funtr, funlift =
         match which with
         | `Right -> (zero, one, ftrr, fliftr, ftrl, fliftl)
         | `Left -> (one, zero, ftrl, fliftl, ftrr, fliftr) in
       let Eq = eq_of_zero_pbij p in
       (* The function argument that we'll be lifting *)
       let f : (((hb, D.zero) snoc, Hott.dim) snoc, kinetic) term =
         Var (Index (Later Now, id_sface D.zero)) in
       (* The arguments of its lifted version *)
       let a0 : (((hb, D.zero) snoc, Hott.dim) snoc, kinetic) term = Var (Index (Now, zero)) in
       let a1 : (((hb, D.zero) snoc, Hott.dim) snoc, kinetic) term = Var (Index (Now, one)) in
       let a2 : (((hb, D.zero) snoc, Hott.dim) snoc, kinetic) term =
         Var (Index (Now, id_sface Hott.dim)) in
       let untr_a1 = app (Field (dom2, funtr, zero_ins Hott.dim)) a1 in
       let unlift_a1 = app (Field (dom2, funlift, zero_ins Hott.dim)) a1 in
       let* a1cube =
         match which with
         | `Right -> Hott.cube untr_a1 a1 unlift_a1
         | `Left -> Hott.cube a1 untr_a1 unlift_a1 in
       let f_untr_a1 = app f untr_a1 in
       let tr_f_untr_a1 = app (Field (App (cod2, a1cube), ftr, zero_ins Hott.dim)) f_untr_a1 in
       let lift_f_untr_a1 = app (Field (App (cod2, a1cube), flift, zero_ins Hott.dim)) f_untr_a1 in
       let a00, a01, a02 = (a0, a1, a2) in
       let a10, a11, a12 = (untr_a1, a1, unlift_a1) in
       let* atube =
         match which with
         | `Right -> Hott.tube12 hh a00 a01 a02 a10 a11 a12
         | `Left -> Hott.tube12 hh a01 a00 a02 a11 a10 a12 in
       let dom_tubed = Inst (Act (Act (dom2, refl), sym), atube) in
       let a21 = Act (a1, refl) in
       let a20 = app (Field (dom_tubed, funtr, zero_ins Hott.dim)) a21 in
       let sym_a22 = Act (app (Field (dom_tubed, funlift, zero_ins Hott.dim)) a21, sym) in
       let* a22cube =
         match which with
         | `Right -> Hott.cube2 hh a00 a10 a20 a01 a11 a21 a02 a12 sym_a22
         | `Left -> Hott.cube2 hh a01 a11 a21 a00 a10 a20 a02 a12 sym_a22 in
       let cod22 = App (Act (cod2, refl), a22cube) in
       (* The final transport is *always* a trl, for both cases (liftr and liftl), so this is Hott.cube in both cases. *)
       let* ax0 = Hott.cube a00 a10 a20 in
       let tr_reflf_a20 = Act (tr_f_untr_a1, refl) in
       let* btube =
         match which with
         | `Right ->
             Hott.tube12 hh (app f a00) (app f a10)
               (App (Act (f, refl), ax0))
               tr_f_untr_a1 tr_f_untr_a1 tr_reflf_a20
         | `Left ->
             Hott.tube12 hh tr_f_untr_a1 tr_f_untr_a1 tr_reflf_a20 (app f a00) (app f a10)
               (App (Act (f, refl), ax0)) in
       plusfam
         (Lam
            ( fname,
              Lam
                ( xsname,
                  Realize
                    (app (Field (Inst (cod22, btube), ftrl, zero_ins Hott.dim)) lift_f_untr_a1) ) ))
     in
     let liftr = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> lift `Right p) } in
     let liftl = PlusPbijmap.build D.zero Hott.dim { build = (fun p -> lift `Left p) } in
     (* The corecursive field, which transports across an isomorphism to an iterated pi-type. *)
     let id : type r. (D.zero, Hott.dim, r) pbij -> (r, ((emp, D.zero) snoc, D.zero) snoc) PlusFam.t
         =
      fun p ->
       let Eq = eq_of_zero_pbij p in
       let [ f0name; f1name; f2name; x0name; x1name; x2name ] =
         Vec.map
           (fun str -> singleton_variables D.zero (Some str))
           [ "f0"; "f1"; "f2"; "x0"; "x1"; "x2" ] in
       let hb00 = Plusmap.OfDom.suc (Plusmap.OfDom.suc hb D.zero) D.zero in
       (* In context f0,f1,x0,x1 *)
       let x0 = Var (Index (Later Now, id_sface D.zero)) in
       let x1 = Var (Index (Now, id_sface D.zero)) in
       let* xtube = Hott.tube x0 x1 in
       (* In context f0,f1,x0,x1,x2  *)
       let x0 = Weaken x0 in
       let x1 = Weaken x1 in
       let f0 = Var (Index (Later (Later (Later (Later Now))), id_sface D.zero)) in
       let f1 = Var (Index (Later (Later (Later Now)), id_sface D.zero)) in
       let x2 = Var (Index (Now, id_sface D.zero)) in
       let* xcube = Hott.cube x0 x1 x2 in
       let f0x0 = app f0 x0 in
       let f1x1 = app f1 x1 in
       let* fxtube = Hott.tube f0x0 f1x1 in
       let fib =
         Pi
           ( Some "x0",
             CubeOf.singleton dom0,
             CodCube.singleton
               (Pi
                  ( Some "x1",
                    CubeOf.singleton (Weaken dom1),
                    CodCube.singleton
                      (Pi
                         ( Some "x2",
                           CubeOf.singleton (Inst (Weaken (Weaken dom2), xtube)),
                           CodCube.singleton
                             (Inst (App (Weaken (Weaken (Weaken cod2)), xcube), fxtube)) )) )) )
       in
       (* In context f0,f1,f2,x0,x1,x2 *)
       let x0 = Var (Index (Later (Later Now), id_sface D.zero)) in
       let x1 = Var (Index (Later Now, id_sface D.zero)) in
       let x2 = Var (Index (Now, id_sface D.zero)) in
       let* xcube = Hott.cube x0 x1 x2 in
       let f2 = Var (Index (Later (Later (Later Now)), id_sface D.zero)) in
       let fro_fn = Lam (f2name, Lam (x0name, Lam (x1name, Lam (x2name, App (f2, xcube))))) in
       (* In context f0, f1, x *)
       let f2 = Var (Index (Later Now, id_sface D.zero)) in
       let x_0 = Var (Index (Now, zero)) in
       let x_1 = Var (Index (Now, one)) in
       let x_2 = Var (Index (Now, id_sface Hott.dim)) in
       let to_fn =
         Lam (f2name, Lam (singleton_variables Hott.dim (Some "x"), app (app (app f2 x_0) x_1) x_2))
       in
       let* fields = fib_iso hb00 ~fib ~to_fn ~fro_fn in
       plusfam
         (Lam
            (f0name, Lam (f1name, Struct { dim = D.zero; eta = Noeta; energy = Potential; fields })))
     in
     let id = PlusPbijmap.build D.zero Hott.dim { build = id } in
     return
       (Emp
       <: StructfieldAbwd.Entry (ftrr, Higher trr)
       <: Entry (fliftr, Higher liftr)
       <: Entry (ftrl, Higher trl)
       <: Entry (fliftl, Higher liftl)
       <: Entry (fid, Higher id)))

module Codata = struct
  type (_, _, _, _) t =
    | Fibrancy : ('g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy -> ('g, 'n, 'b, 'et) t

  let empty : type g n b et.
      g D.t ->
      n D.t ->
      b Plusmap.OfDom.t ->
      (potential, et) eta ->
      (b, kinetic) term ->
      (g, n, b, et) t =
   fun glue dim length eta ty ->
    let (Exists (type hb) ((_hb, plusmap) : hb Plusmap.OfCod.t * (Hott.dim, b, hb) Plusmap.t)) =
      Plusmap.exists Hott.dim length in
    let (Plus dimh) = D.plus Hott.dim in
    Fibrancy
      {
        glue;
        dim;
        length;
        plusmap;
        ty;
        eta;
        dimh;
        fields = Emp;
        trr = Emp;
        trl = Emp;
        liftr = Emp;
        liftl = Emp;
      }

  let add_field : type g n b et.
      (g, n, b, et) t -> (b * g * et) CodatafieldAbwd.entry -> (g, n, b, et) t =
   fun (Fibrancy (type nh hb) (f : (g, n, nh, b, hb, et) codata_fibrancy)) (Entry (fld, fldty)) ->
    let x = Var (Index (Now, id_sface D.zero)) in
    let ins = zero_ins Hott.dim in
    let onx : Hott.dim Field.t -> ((hb, D.zero) snoc, kinetic) term =
     fun trlift -> app (Field (Weaken (Shift (Hott.dim, f.plusmap, f.ty)), trlift, ins)) x in
    let trr_x, liftr_x, trl_x, liftl_x = (onx ftrr, onx fliftr, onx ftrl, onx fliftl) in
    match (Hott.cube x trr_x liftr_x, Hott.cube trl_x x liftl_x) with
    | Some xrcube, Some xlcube ->
        let trlift : type m.
            Hott.dim Field.t ->
            (Hott.dim, ((hb, D.zero) snoc, kinetic) term) CubeOf.t ->
            (m * (hb, D.zero) snoc * potential * et) StructfieldAbwd.entry =
         fun trlift xcube ->
          match fldty with
          | Lower ty ->
              let sty = Shift (Hott.dim, f.plusmap, Lam (singleton_variables f.glue None, ty)) in
              StructfieldAbwd.Entry
                ( fld,
                  Lower
                    ( Realize
                        (app
                           (Field (App (Weaken sty, xcube), trlift, ins))
                           (Field (x, fld, ins_zero f.dim))),
                      `Labeled ) )
          | Higher _ ->
              let open Reporter in
              fatal ~severity:Asai.Diagnostic.Bug (Unimplemented "higher fields of transport")
         (* TODO: Once it's written, call this from Check.check_codata too. *)
         (* Entry (f, Higher _) *) in
        let new_trr, new_liftr, new_trl, new_liftl =
          (trlift ftrr xrcube, trlift fliftr xrcube, trlift ftrl xlcube, trlift fliftl xlcube) in
        Fibrancy
          {
            f with
            fields = Snoc (f.fields, Entry (fld, fldty));
            trr = Snoc (f.trr, new_trr);
            liftr = Snoc (f.liftr, new_liftr);
            trl = Snoc (f.trl, new_trl);
            liftl = Snoc (f.liftl, new_liftl);
          }
    | _ -> Fibrancy f

  let rec finish : type g n nh b hb et.
      (g, n, nh, b, hb, et) codata_fibrancy -> (g * b * potential * no_eta) StructfieldAbwd.t =
   fun { glue; dim; length; plusmap; ty; eta; dimh; fields; trr; trl; liftr; liftl } ->
    let xname = singleton_variables D.zero (Some "x") in
    let yname = singleton_variables D.zero (Some "y") in
    let plusfam x = Some (PlusFam.PlusFam (plusmap, x)) in
    let _pluszero x = Some (PlusFam.PlusFam (Plusmap.zerol length, x)) in
    let tr : type r.
        [ `Left | `Right ] ->
        (n * (hb, D.zero) snoc * potential * et) StructfieldAbwd.t ->
        (g, Hott.dim, r) pbij ->
        (r, b) PlusFam.t =
     fun _which fields p ->
      match singleton_pbij p Hott.singleton with
      (* This is the "tr.e" case when we just pass off to the type of the field. *)
      | Left -> plusfam (Lam (xname, Struct { dim; eta; energy = Potential; fields }))
      (* This is the tr.1/tr.2 case when we use the bisimulation data supplied. *)
      | Right _ins -> None
     (* pluszero @@ Lam (xname, _) *) in
    let trr = PlusPbijmap.build glue Hott.dim { build = (fun p -> tr `Right trr p) } in
    let trl = PlusPbijmap.build glue Hott.dim { build = (fun p -> tr `Left trl p) } in
    let dimh = D.plus_out dim dimh in
    let lift : type r.
        [ `Left | `Right ] ->
        (nh * (hb, D.zero) snoc * potential * et) StructfieldAbwd.t ->
        (g, Hott.dim, r) pbij ->
        (r, b) PlusFam.t =
     fun _which fields p ->
      match singleton_pbij p Hott.singleton with
      | Left -> plusfam (Lam (xname, Struct { dim = dimh; eta; energy = Potential; fields }))
      | Right _ins -> None
     (* pluszero @@ Lam (xname, _) *) in
    let liftr = PlusPbijmap.build glue Hott.dim { build = (fun p -> lift `Right liftr p) } in
    let liftl = PlusPbijmap.build glue Hott.dim { build = (fun p -> lift `Left liftl p) } in
    let id : type r. (g, Hott.dim, r) pbij -> (r, b) PlusFam.t =
     fun p ->
      match singleton_pbij p Hott.singleton with
      | Left -> (
          match D.compare_zero glue with
          | Zero ->
              let hlength = Plusmap.out Hott.dim length plusmap in
              let hlength00 = Plusmap.OfDom.suc (Plusmap.OfDom.suc hlength D.zero) D.zero in
              let x0 = Var (Index (Later (Later Now), id_sface D.zero)) in
              let x1 = Var (Index (Later Now, id_sface D.zero)) in
              let x2 = Var (Index (Now, id_sface D.zero)) in
              let* xtube = Hott.tube x0 x1 in
              let* xcube = Hott.cube x0 x1 x2 in
              let folder :
                  (g, nh, ((hb, D.zero) snoc, D.zero) snoc, et) t ->
                  (b * g * et) CodatafieldAbwd.entry ->
                  (g, nh, ((hb, D.zero) snoc, D.zero) snoc, et) t =
               fun fields (CodatafieldAbwd.Entry (fld, fldty)) ->
                match fldty with
                | Lower fldty ->
                    let xsname = singleton_variables D.zero (Some "x") in
                    add_field fields
                      (CodatafieldAbwd.Entry
                         ( fld,
                           Lower
                             (Inst
                                ( App
                                    ( Weaken
                                        (Weaken
                                           (Weaken (Shift (Hott.dim, plusmap, Lam (xsname, fldty))))),
                                      xcube ),
                                  TubeOf.mmap { map = (fun _ [ x ] -> field x fld) } [ xtube ] )) ))
                | Higher _ ->
                    (* TODO *)
                    fields in
              let x0 = Var (Index (Later Now, id_sface D.zero)) in
              let x1 : (((hb, D.zero) snoc, D.zero) snoc, kinetic) term =
                Var (Index (Now, id_sface D.zero)) in
              let* xtube = Hott.tube x0 x1 in
              let (Fibrancy fields) =
                Bwd.fold_left folder
                  (empty glue dimh hlength00 eta
                     (Inst (Weaken (Weaken (Shift (Hott.dim, plusmap, ty))), xtube)))
                  fields in
              let fields = finish fields in
              plusfam
              @@ Lam
                   ( xname,
                     Lam (yname, Struct { dim = glue; eta = Noeta; energy = Potential; fields }) )
          | Pos _ ->
              (* The bisim .id case *)
              None)
      | Right _ins -> None
     (* pluszero @@ Lam (xname, _) *) in
    let id = lazy (PlusPbijmap.build glue Hott.dim { build = (fun p -> id p) }) in
    Emp
    <: StructfieldAbwd.Entry (ftrr, Higher trr)
    <: Entry (fliftr, Higher liftr)
    <: Entry (ftrl, Higher trl)
    <: Entry (fliftl, Higher liftl)
    <: Entry (fid, LazyHigher id)
end

let universe : (D.zero * emp * potential * no_eta) StructfieldAbwd.t option Lazy.t =
  Lazy.from_val None

let data : unit option Lazy.t = Lazy.from_val None
