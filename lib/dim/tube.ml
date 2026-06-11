open Bwd
open Util
open Signatures
open Tlist
open Hlist
open Singleton
open Cube
open Sface
open Tface

(* Tube data structures *)

module Tube (F : Fam2) = struct
  module C = Cube (F)
  open C.Infix

  (* An (n,k,n+k)-tube is like a (n+k)-cube but where the top k indices (the "instantiated" ones) are not all maximal.  Hence if k=0 it is empty, while if n=0 it contains everything except the top face.  An (m,k,m+k,w)-gtube is the part of such a tube with k dimensions left to be instantiated and m uninstantiated, m+k total dimensions left, and 'w the word of dimensions already decided (taken as Mid) on the path leading to it, as in Cube.  The ends of a Branch are complete cubes over the remaining dimensions; the mid adds its generator at the inner end of the decided word, with the witness stored in the Branch. *)
  type (_, _, _, _, _) gt =
    | Leaf : 'n D.t -> ('n, D.zero, 'n, 'w, 'b) gt
    | Branch :
        'g D.G.t
        * ((D.zero, 'g) D.suc, 'w, 'gw) D.plus
        * 'l Endpoints.len
        * (('mk, 'w, 'b) C.gt, 'l) Bwv.t
        * ('m, 'k, 'mk, 'gw, 'b) gt
        -> ('m, ('k, 'g) D.suc, ('mk, 'g) D.suc, 'w, 'b) gt

  (* This definition gives a cardinality F(k,m) for (m,k,m+k,w,b) gtube with recurrence relations

     F(0,m) = 0
     F(k+1,m) = 3^(m+k) * 2 + F(k,m)

     Therefore, we can compute examples like

     F(1,m) = 3^m * 2 + F(0,m) = 3^m * 2 + 0 = 3^m * 2 = 3^(m+1) - 3^m
     F(2,m) = 3^(m+1) * 2 + F(1,m) = (3^(m+1) + 3^m) * 2 = (3^(m+2) + 3^(m+1)) - (3^(m+1) + 3^m) = 3^(m+2) - 3^m

     and so on, in general

     F(k,m) = 3^(m+k) - 3^m
  *)

  type ('n, 'k, 'nk, 'b) t = ('n, 'k, 'nk, D.zero, 'b) gt

  (* In a tube we always have m + k = m+k. *)

  let rec gplus : type m k mk w b. (m, k, mk, w, b) gt -> (m, k, mk) D.plus = function
    | Leaf _ -> Zero
    | Branch (g, _, _, _, mid) -> Suc (gplus mid, g)

  let plus : type m k mk b. (m, k, mk, b) t -> (m, k, mk) D.plus = fun t -> gplus t

  (* The constituents of a tube are valid dimensions. *)

  let inst : type m k mk b. (m, k, mk, b) t -> k D.t = fun t -> Word (plus t)

  let rec guninst : type m k mk w b. (m, k, mk, w, b) gt -> m D.t = function
    | Leaf m -> m
    | Branch (_, _, _, _, mid) -> guninst mid

  let uninst : type m k mk b. (m, k, mk, b) t -> m D.t = fun t -> guninst t
  let out : type m k mk b. (m, k, mk, b) t -> mk D.t = fun t -> D.plus_out (uninst t) (plus t)

  (* The empty tube, with nothing instantiated *)

  let empty : type n b. n D.t -> (n, D.zero, n, b) t = fun n -> Leaf n

  (* A full tube of some dimension, with everything instantiated. *)
  type _ full = Full_tube : (D.zero, 'n, 'n, 'a) t -> 'a full
  type (_, _) some = Some_tube : ('n, 'k, 'nk, 'a) t -> ('nk, 'a) some
  type _ any = Any_tube : ('n, 'k, 'nk, 'a) t -> 'a any

  let is_full : type m k mk b. (m, k, mk, b) t -> bool =
   fun t ->
    match D.compare (uninst t) D.zero with
    | Eq -> true
    | Neq -> false

  (* Looking up with a tface.  The carried plus relation (j, w, p) is transported exactly as in Cube.gfind. *)

  let rec gfind : type m k mk w b j p.
      (m, k, mk, w, b) gt -> (j, m, k, mk) tface -> (j, w, p) D.plus -> (p, b) F.t =
   fun tr d jw ->
    match (tr, d) with
    | Leaf _, _ -> .
    | Branch (_, _, l1, ends, _), End (d, _, _, (l2, e)) ->
        let Eq = Endpoints.uniq l1 l2 in
        C.gfind (Bwv.nth e ends) d jw
    | Branch (_, pw, _, _, mid), Mid (d, g) -> gfind mid d (D.plus_assocr (Suc (Zero, g)) pw jw)

  let find : type m n k nk b. (n, k, nk, b) t -> (m, n, k, nk) tface -> (m, b) F.t =
   fun tr d -> gfind tr d Zero

  (* The boundary of a cube is a maximal tube. *)

  let rec gboundary : type m w b. (m, w, b) C.gt -> (D.zero, m, m, w, b) gt = function
    | Leaf _ -> Leaf D.zero
    | Branch (g, pw, l, ends, mid) -> Branch (g, pw, l, ends, gboundary mid)

  let boundary : type n b. (n, b) C.t -> (D.zero, n, n, b) t = fun tr -> gboundary tr

  (* We can also pick out a less-instantiated part of a tube *)

  let rec gpboundary : type m k mk l kl mkl w b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, w, b) gt -> (mk, l, mkl, w, b) gt =
   fun mk kl tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        Leaf (D.plus_out (guninst tr) mk)
    | Suc (kl, _), Branch (g, pw, l, ends, mid) -> Branch (g, pw, l, ends, gpboundary mk kl mid)

  let pboundary : type m k mk l kl mkl b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, b) t -> (mk, l, mkl, b) t =
   fun mk kl tr -> gpboundary mk kl tr

  (* A tube that instantiates exactly one dimension is equivalently a Bwv of cubes. *)
  let of_cube_bwv : type n k nk b l.
      n D.t ->
      k is_singleton ->
      (n, k, nk) D.plus ->
      l Endpoints.len ->
      ((n, b) C.t, l) Bwv.t ->
      (n, k, nk, b) t =
   fun n k nk l cubes ->
    let One, Suc (Zero, g) = (k, nk) in
    Branch (g, Zero, l, cubes, Leaf n)

  let to_cube_bwv : type n k nk b l.
      k is_singleton -> l Endpoints.len -> (n, k, nk, b) t -> ((n, b) C.t, l) Bwv.t =
   fun k l tube ->
    let One = k in
    let (Branch (_, _, l', cubes, Leaf _)) = tube in
    let Eq = Endpoints.uniq l l' in
    cubes

  (* Heterogeneous lists and multimaps *)

  (* The structure of hlists for tubes is exactly parallel to that for cubes. *)
  module Heter = struct
    type (_, _, _, _, _) hgt =
      | [] : ('m, 'k, 'mk, 'w, nil) hgt
      | ( :: ) :
          ('m, 'k, 'mk, 'w, 'x) gt * ('m, 'k, 'mk, 'w, 'xs) hgt
          -> ('m, 'k, 'mk, 'w, ('x, 'xs) cons) hgt

    type (_, _, _) ends =
      | Ends :
          'l Endpoints.len * ('mk, 'w, 'bs, 'hs) C.Heter.hgts * ('hs, 'l) Bwv.Heter.ht
          -> ('mk, 'w, 'bs) ends

    let rec ends : type m k mk g w bs.
        (m, (k, g) D.suc, (mk, g) D.suc, w, bs) hgt -> (mk, w, bs) ends = function
      | [] ->
          let (Wrap l) = Endpoints.wrapped () in
          Ends (l, Nil, [])
      | Branch (_, _, l1, es, _) :: xs ->
          let (Ends (l2, hs, ess)) = ends xs in
          let Eq = Endpoints.uniq l1 l2 in
          Ends (l2, Cons hs, es :: ess)

    let rec mid : type m k mk g w gw bs.
        ((D.zero, g) D.suc, w, gw) D.plus ->
        (m, (k, g) D.suc, (mk, g) D.suc, w, bs) hgt ->
        (m, k, mk, gw, bs) hgt =
     fun pw xss ->
      match xss with
      | [] -> []
      | Branch (_, pw', _, _, m) :: xs ->
          let Eq = D.plus_uniq pw pw' in
          m :: mid pw xs

    let rec leaf : type n w bs. n D.t -> bs Tlist.t -> (n, D.zero, n, w, bs) hgt =
     fun n bs ->
      match bs with
      | Nil -> []
      | Cons bs -> Leaf n :: leaf n bs

    let rec branch : type m k mk g w gw bs hs l.
        g D.G.t ->
        ((D.zero, g) D.suc, w, gw) D.plus ->
        l Endpoints.len ->
        (mk, w, bs, hs) C.Heter.hgts ->
        (hs, l) Bwv.Heter.ht ->
        (m, k, mk, gw, bs) hgt ->
        (m, (k, g) D.suc, (mk, g) D.suc, w, bs) hgt =
     fun g pw l hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids ->
          Branch (g, pw, l, ends, mid) :: branch g pw l hs endss mids
  end

  module Infix = C.Infix

  (* Now the generic traversal.  There are two phases.  The first walks down the instantiated dimensions of the tube, accumulating the word 'a of dimensions decided as Mid so far.  Whenever it takes an End, everything below is an ordinary cube traversal; the second phase performs that traversal while accumulating the *inner* part of the eventual tface's payload strict face, and assembles the complete tface at each leaf using the End data and the Mid-prefix recorded by the first phase.  All the bookkeeping is associativity of word concatenation. *)

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)
    module BwvM = Bwv.Applicatic (M)

    type ('n, 'k, 'nk, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'cs) C.Heter.hft M.t;
    }

    (* The cube phase.  Fixed throughout: the tface End data (generator g0 and endpoint e0), the payload split nk1 : (n, k1, mk1), and the Mid-prefix relations pa and pnk recorded when the End was taken.  Maintained: the (m, c, mk1) plus relating the remaining height to the consumed part of the cube, the partial payload face s : (w, c) sface, and the witness wia : (w, a, wc) relating the payload domain to the decided word wc indexing the trees. *)
    let rec gpmapM_cube : type m c w wc a g0 k1 mk1 n k nk b bs cs l0.
        (m, c, mk1) D.plus ->
        (w, c) sface ->
        (w, a, wc) D.plus ->
        (n, k1, mk1) D.plus ->
        ((k1, g0) D.suc, a, k) D.plus ->
        ((mk1, g0) D.suc, a, nk) D.plus ->
        g0 D.G.t ->
        l0 Endpoints.t ->
        (n, k, nk, (b, bs) cons, cs) pmapperM ->
        (m, wc, (b, bs) cons) C.Heter.hgt ->
        cs Tlist.t ->
        (m, wc, cs) C.Heter.hgt M.t =
     fun mc s wia nk1 pa pnk g0 e0 g trs cst ->
      match trs with
      | Leaf _ :: _ ->
          let Eq = D.zero_plus_uniq mc in
          M.apply (g.map (tface_plus (End (s, nk1, g0, e0)) pa pnk wia) (C.Heter.lab trs))
          @@ fun x -> C.Heter.leaf x
      | Branch (g1, pw, _, _, _) :: _ ->
          let (Ends (l, hs, ends)) = C.Heter.ends trs in
          let mid = C.Heter.mid pw trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let (Plus plc) = D.plus (cod_sface s) in
          let (Plus pwd) = D.plus (dom_sface s) in
          let mc' = D.plus_assocr (Suc (Zero, g1)) plc mc in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.pmapM
                   (fun (e :: brs) ->
                     M.apply
                       (gpmapM_cube mc'
                          (sface_plus_sface (End (Zero, g1, e)) plc (D.zero_plus (dom_sface s)) s)
                          wia nk1 pa pnk g0 e0 g (C.Heter.hgt_of_hlist hs brs) cst)
                     @@ fun xs -> C.Heter.hlist_of_hgt newhs xs)
                   (Endpoints.indices l :: ends) (C.Heter.tlist_hgts newhs cst))
               (fun () ->
                 gpmapM_cube mc'
                   (sface_plus_sface (Mid (Zero, g1)) plc pwd s)
                   (D.plus_assocl pwd wia pw) nk1 pa pnk g0 e0 g mid cst))
          @@ fun (newends, newmid) -> C.Heter.branch g1 pw l newhs newends newmid

    (* The tube phase, walking the instantiated dimensions.  Maintained: the payload split nk1 : (n, k1, mk1) of the remaining dimensions, and the Mid-prefix relations pa : (k1, a, k) and pnk : (mk1, a, nk) recording how the decided word 'a sits inside the instantiated and total dimensions. *)
    let rec gpmapM_r : type n k1 mk1 a k nk b bs cs.
        (n, k1, mk1) D.plus ->
        (k1, a, k) D.plus ->
        (mk1, a, nk) D.plus ->
        (n, k, nk, (b, bs) cons, cs) pmapperM ->
        (n, k1, mk1, a, (b, bs) cons) Heter.hgt ->
        (* A special Applicative action to take for dimensions that have zero arity *)
        ?ifzero:unit M.t ->
        cs Tlist.t ->
        (n, k1, mk1, a, cs) Heter.hgt M.t =
     fun nk1 pa pnk g trs ?ifzero cst ->
      match (nk1, trs) with
      | Zero, Leaf n :: _ -> return (Heter.leaf n cst)
      | Suc (nk1', g0), Branch (_, pw, _, _, _) :: _ ->
          let (Ends (l, hs, ends)) = Heter.ends trs in
          let mid = Heter.mid pw trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          let a_run = D.plus_right pa in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.pmapM
                   (fun (e :: brs) ->
                     M.apply
                       (gpmapM_cube Zero Zero (D.zero_plus a_run) nk1' pa pnk g0 e g
                          (C.Heter.hgt_of_hlist hs brs) cst)
                     @@ fun xs -> C.Heter.hlist_of_hgt newhs xs)
                   (Endpoints.indices l :: ends) (C.Heter.tlist_hgts newhs cst))
               (fun () ->
                 M.zip
                   (fun () ->
                     match (Endpoints.len l, ifzero) with
                     | N.Nat Zero, Some ifzero -> ifzero
                     | _ -> return ())
                   (fun () ->
                     gpmapM_r nk1'
                       (D.plus_assocr (Suc (Zero, g0)) pw pa)
                       (D.plus_assocr (Suc (Zero, g0)) pw pnk)
                       g mid ?ifzero cst)))
          @@ fun (newends, ((), newmid)) -> Heter.branch g0 pw l newhs newends newmid

    let pmapM : type n k nk b bs cs.
        (n, k, nk, (b, bs) cons, cs) pmapperM ->
        (n, k, nk, D.zero, (b, bs) cons) Heter.hgt ->
        ?ifzero:unit M.t ->
        cs Tlist.t ->
        (n, k, nk, D.zero, cs) Heter.hgt M.t =
     fun g trs ?ifzero cst ->
      let (tr :: _) = trs in
      gpmapM_r (plus tr) Zero Zero g trs ?ifzero cst

    (* And now the more specialized versions. *)

    type ('n, 'k, 'nk, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'c) F.t M.t;
    }

    let mmapM : type n k nk b bs c.
        (n, k, nk, (b, bs) cons, c) mmapperM ->
        ?ifzero:unit M.t ->
        (n, k, nk, D.zero, (b, bs) cons) Heter.hgt ->
        (n, k, nk, c) t M.t =
     fun g ?ifzero xs ->
      M.apply
        (pmapM
           { map = (fun fa x -> M.apply (g.map fa x) @@ fun y -> y @: []) }
           xs ?ifzero (Cons Nil))
      @@ fun [ ys ] -> ys

    type ('n, 'k, 'nk, 'bs) miteratorM = {
      it : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> unit M.t;
    }

    let miterM : type n k nk b bs.
        (n, k, nk, (b, bs) cons) miteratorM ->
        ?ifzero:unit M.t ->
        (n, k, nk, D.zero, (b, bs) cons) Heter.hgt ->
        unit M.t =
     fun g ?ifzero xs ->
      M.apply (pmapM { map = (fun fa x -> M.apply (g.it fa x) @@ fun () -> hnil) } xs ?ifzero Nil)
      @@ fun [] -> ()

    (* We also have a monadic builder function *)

    type ('n, 'k, 'nk, 'b) builderM = { build : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'b) F.t M.t }

    (* The cube phase of building, mirroring gpmapM_cube. *)
    let rec gbuildM_cube : type m c w wc a g0 k1 mk1 n k nk b l0.
        m D.t ->
        (m, c, mk1) D.plus ->
        (w, c) sface ->
        (w, a, wc) D.plus ->
        (n, k1, mk1) D.plus ->
        ((k1, g0) D.suc, a, k) D.plus ->
        ((mk1, g0) D.suc, a, nk) D.plus ->
        g0 D.G.t ->
        l0 Endpoints.t ->
        (n, k, nk, b) builderM ->
        (m, wc, b) C.gt M.t =
     fun m mc s wia nk1 pa pnk g0 e0 g ->
      match m with
      | Word Zero ->
          let Eq = D.zero_plus_uniq mc in
          M.apply (g.build (tface_plus (End (s, nk1, g0, e0)) pa pnk wia)) @@ fun x -> C.Leaf x
      | Word (Suc (m1, g1)) ->
          let (Plus plc) = D.plus (cod_sface s) in
          let (Plus pwd) = D.plus (dom_sface s) in
          let (Plus pwc) = D.plus (D.plus_out (dom_sface s) wia) in
          let mc' = D.plus_assocr (Suc (Zero, g1)) plc mc in
          let (Wrap l) = Endpoints.wrapped () in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.mapM
                   (fun e ->
                     gbuildM_cube (Word m1) mc'
                       (sface_plus_sface (End (Zero, g1, e)) plc (D.zero_plus (dom_sface s)) s)
                       wia nk1 pa pnk g0 e0 g)
                   (Endpoints.indices l))
               (fun () ->
                 gbuildM_cube (Word m1) mc'
                   (sface_plus_sface (Mid (Zero, g1)) plc pwd s)
                   (D.plus_assocl pwd wia pwc) nk1 pa pnk g0 e0 g))
          @@ fun (ends, mid) -> C.Branch (g1, pwc, l, ends, mid)

    (* The tube phase of building, mirroring gpmapM_r. *)
    let rec gbuildM_r : type n k1 mk1 a k nk b.
        n D.t ->
        (n, k1, mk1) D.plus ->
        (k1, a, k) D.plus ->
        (mk1, a, nk) D.plus ->
        (n, k, nk, b) builderM ->
        (n, k1, mk1, a, b) gt M.t =
     fun n nk1 pa pnk g ->
      match nk1 with
      | Zero -> return (Leaf n)
      | Suc (nk1', g0) ->
          let a_run = D.plus_right pa in
          let (Plus pw) = D.plus a_run in
          let (Wrap l) = Endpoints.wrapped () in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.mapM
                   (fun e ->
                     gbuildM_cube (D.plus_out n nk1') Zero Zero (D.zero_plus a_run) nk1' pa pnk g0 e
                       g)
                   (Endpoints.indices l))
               (fun () ->
                 gbuildM_r n nk1'
                   (D.plus_assocr (Suc (Zero, g0)) pw pa)
                   (D.plus_assocr (Suc (Zero, g0)) pw pnk)
                   g))
          @@ fun (ends, mid) -> Branch (g0, pw, l, ends, mid)

    let buildM : type n k nk b.
        n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) builderM -> (n, k, nk, b) t M.t =
     fun n nk g -> gbuildM_r n nk Zero Zero g
  end

  module Monadic (M : Monad.Plain) = struct
    module A = Applicative.OfMonad (M)
    include Applicatic (A)
  end

  (* Now we deduce the non-monadic versions *)

  module IdM = Monadic (Monad.Identity)

  let pmap : type n k nk b bs cs.
      (n, k, nk, (b, bs) cons, cs) IdM.pmapperM ->
      (n, k, nk, D.zero, (b, bs) cons) Heter.hgt ->
      cs Tlist.t ->
      (n, k, nk, D.zero, cs) Heter.hgt =
   fun g trs cst -> IdM.pmapM g trs cst

  let mmap : type n k nk b bs c.
      (n, k, nk, (b, bs) cons, c) IdM.mmapperM ->
      (n, k, nk, D.zero, (b, bs) cons) Heter.hgt ->
      (n, k, nk, c) t =
   fun g xs -> IdM.mmapM g xs

  let miter : type n k nk b bs.
      (n, k, nk, (b, bs) cons) IdM.miteratorM -> (n, k, nk, D.zero, (b, bs) cons) Heter.hgt -> unit
      =
   fun g xs -> IdM.miterM g xs

  let build : type n k nk b.
      n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) IdM.builderM -> (n, k, nk, b) t =
   fun n nk g -> IdM.buildM n nk g
end

module TubeOf = struct
  include Tube (FamOf)

  (* We can lift and lower a tube too *)

  let rec glift : type m k mk w1 n2 w12 b.
      (w1, n2, w12) D.plus -> (m, k, mk, w1, b) gt -> (m, k, mk, w12, b) gt =
   fun w12 tr ->
    match tr with
    | Leaf m -> Leaf m
    | Branch (g, pw, l, ends, mid) ->
        let (Plus q) = D.plus (D.plus_right w12) in
        let pw' = D.plus_assocr pw w12 q in
        Branch (g, pw', l, Bwv.map (fun t -> CubeOf.lift w12 t) ends, glift q mid)

  let rec glower : type m k mk w1 n2 w12 b.
      (m, k, mk, w12, b) gt -> (w1, n2, w12) D.plus -> (m, k, mk, w1, b) gt =
   fun tr w12 ->
    match tr with
    | Leaf m -> Leaf m
    | Branch (g, pw, l, ends, mid) ->
        let w1 = D.plus_left w12 (D.plus_right pw) in
        let (Plus pw') = D.plus w1 in
        let q = D.plus_assocl pw' w12 pw in
        Branch (g, pw', l, Bwv.map (fun t -> CubeOf.lower t w12) ends, glower mid q)

  (* We can fill in the missing pieces of a tube with a cube, yielding a cube.  The witness (l, w, lw) records how the decided word of the filling cube extends that of the tube. *)

  let rec gplus_gcube : type m l ml w lw b.
      (l, w, lw) D.plus -> (m, l, ml, w, b) gt -> (m, lw, b) C.gt -> (ml, w, b) C.gt =
   fun lw tl tm ->
    match tl with
    | Leaf _ ->
        let Eq = D.zero_plus_uniq lw in
        tm
    | Branch (g, pw, l, ends, mid) ->
        Branch (g, pw, l, ends, gplus_gcube (D.plus_assocr (Suc (Zero, g)) pw lw) mid tm)

  let plus_cube : type m l ml b. (m, l, ml, b) t -> (m, b) C.t -> (ml, b) C.t =
   fun tl tm ->
    let l_run = D.plus_right (gplus tl) in
    gplus_gcube Zero tl (CubeOf.lift (D.zero_plus l_run) tm)

  (* Or we can fill in some of those missing pieces with a tube instead, yielding another tube.  The witness (l, w, lw) records how the decided word of the inner tube extends that of the outer one. *)

  let rec gplus_gtube : type m k mk l kl mkl w lw b.
      (k, l, kl) D.plus ->
      (l, w, lw) D.plus ->
      (mk, l, mkl, w, b) gt ->
      (m, k, mk, lw, b) gt ->
      (m, kl, mkl, w, b) gt =
   fun kl lw tl tk ->
    match (kl, tl) with
    | Zero, Leaf _ ->
        let Eq = D.zero_plus_uniq lw in
        tk
    | Suc (kl, g), Branch (g', pw, l, ends, mid) ->
        Branch (g', pw, l, ends, gplus_gtube kl (D.plus_assocr (Suc (Zero, g)) pw lw) mid tk)

  let plus_tube : type m k mk l kl mkl b.
      (k, l, kl) D.plus -> (mk, l, mkl, b) t -> (m, k, mk, b) t -> (m, kl, mkl, b) t =
   fun kl tl tk ->
    let l_run = D.plus_right kl in
    gplus_gtube kl Zero tl (glift (D.zero_plus l_run) tk)

  (* We can also pick out a lower-dimensional part around the middle of a tube, as well as the outer tube around it.  The witness (l, w, lw) records the decided word of the inner part relative to the outer. *)

  let rec gsplit : type m k mk l kl mkl w lw b.
      (m, k, mk) D.plus ->
      (k, l, kl) D.plus ->
      (l, w, lw) D.plus ->
      (m, kl, mkl, w, b) gt ->
      (m, k, mk, lw, b) gt * (mk, l, mkl, w, b) gt =
   fun mk kl lw tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        let Eq = D.zero_plus_uniq lw in
        (tr, Leaf (D.plus_out (guninst tr) mk))
    | Suc (kl, g), Branch (g', pw, l, ends, mid) ->
        let middle, outer = gsplit mk kl (D.plus_assocr (Suc (Zero, g)) pw lw) mid in
        (middle, Branch (g', pw, l, ends, outer))

  let split : type m k mk l kl mkl b.
      (m, k, mk) D.plus ->
      (k, l, kl) D.plus ->
      (m, kl, mkl, b) t ->
      (m, k, mk, b) t * (mk, l, mkl, b) t =
   fun mk kl tr ->
    let l_run = D.plus_right kl in
    let middle, outer = gsplit mk kl Zero tr in
    (glower middle (D.zero_plus l_run), outer)

  (* Append the elements of a tube, in order, to a given Bwd.t.  For each dimension with zero arity, append the specified element, if any, instead. *)

  let append_bwd : type a m n mn. a Bwd.t -> ?ifzero:a -> (m, n, mn, a) t -> a Bwd.t =
   fun start ?ifzero xs ->
    let module S = struct
      type t = a Bwd.t
    end in
    let module M = Monad.State (S) in
    let open Monadic (M) in
    let ifzero = Option.map (fun x xs -> ((), Snoc (xs, x))) ifzero in
    let (), xs = miterM { it = (fun _ [ x ] xs -> ((), Snoc (xs, x))) } [ xs ] ?ifzero start in
    xs
end
