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

(* Computing the fibrancy fields on canonical type-formers *)

(* We compute these directly as terms.  This puts the onus on us to define them in a well-typed way, but we try our best to copy the definitions that can be given (and typechecked) internally using the higher coinductive isFibrant.  However, in most cases the corecursive case needs to be a (co)recursion at OCaml level, hence we wrap it in LazyHigher to avoid infinite computations.

   The dimension 'n of these Structfields is almost always 0, since it is the substitution dimension of the type being checked against, and canonical types are almost always defined to belong to the 0-dimensional universe.  The one exception, of course, is Gel/glue, where this is the gel dimension.  When n=0, we are proving isFibrant; when n is larger we're proving "refl isFibrant" or some higher version of it.

   The outer laziness is only to delay them until we're inside Dim.Endpoints.run.  Eventually when the HOTT dimension is built-in and always present, that won't be necessary (but we will still need the LazyHigher wrapper around the 'id' field).  *)

(* Pi-types *)

let pi :
    (D.zero * ((emp, D.zero) snoc, D.zero) snoc * potential * no_eta) StructfieldAbwd.t option
    Lazy.t =
  Lazy.from_val None

let universe : (D.zero * emp * potential * no_eta) StructfieldAbwd.t option Lazy.t =
  Lazy.from_val None

let codata : type a n et.
    (a * n * et) CodatafieldAbwd.t -> (n * a * potential * no_eta) StructfieldAbwd.t option Lazy.t =
 fun _ -> Lazy.from_val None

let data : unit option Lazy.t = Lazy.from_val None
