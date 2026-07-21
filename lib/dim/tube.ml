open Bwd
open Util
open Signatures
open Tlist
open Hlist
open Singleton
open Cube
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
        * 'l Endpoints.len
        * (('mk, 'w, 'b) C.gt, 'l) Bwv.t
        * ('m, 'k, 'mk, ('g, 'w) cons, 'b) gt
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

  type ('n, 'k, 'nk, 'b) t = ('n, 'k, 'nk, D.fwd_zero, 'b) gt

  (* In a tube we always have m + k = m+k. *)

  let rec gplus : type m k mk w b. (m, k, mk, w, b) gt -> (m, k, mk) D.plus = function
    | Leaf _ -> Zero
    | Branch (g, _, _, mid) -> Suc (gplus mid, g)

  let plus : type m k mk b. (m, k, mk, b) t -> (m, k, mk) D.plus = fun t -> gplus t

  (* The constituents of a tube are valid dimensions. *)

  let inst : type m k mk b. (m, k, mk, b) t -> k D.t = fun t -> Word (plus t)

  let rec guninst : type m k mk w b. (m, k, mk, w, b) gt -> m D.t = function
    | Leaf m -> m
    | Branch (_, _, _, mid) -> guninst mid

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
      (m, k, mk, w, b) gt -> (j, m, k, mk) tface -> (j, w, p) D.bplus -> (p, b) F.t =
   fun tr d jw ->
    match (tr, d) with
    | Leaf _, _ -> .
    | Branch (_, l1, ends, _), End (d, _, _, (l2, e)) ->
        let Eq = Endpoints.uniq l1 l2 in
        C.gfind (Bwv.nth e ends) d jw
    | Branch (_, _, _, mid), Mid (d, _) -> gfind mid d (Append_cons jw)

  let find : type m n k nk b. (n, k, nk, b) t -> (m, n, k, nk) tface -> (m, b) F.t =
   fun tr d -> gfind tr d Append_nil

  (* The boundary of a cube is a maximal tube. *)

  let rec gboundary : type m w b. (m, w, b) C.gt -> (D.zero, m, m, w, b) gt = function
    | Leaf _ -> Leaf D.zero
    | Branch (g, l, ends, mid) -> Branch (g, l, ends, gboundary mid)

  let boundary : type n b. (n, b) C.t -> (D.zero, n, n, b) t = fun tr -> gboundary tr

  (* We can also pick out a less-instantiated part of a tube *)

  let rec gpboundary : type m k mk l kl mkl w b.
      (m, k, mk) D.plus -> (k, l, kl) D.plus -> (m, kl, mkl, w, b) gt -> (mk, l, mkl, w, b) gt =
   fun mk kl tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        Leaf (D.plus_out (guninst tr) mk)
    | Suc (kl, _), Branch (g, l, ends, mid) -> Branch (g, l, ends, gpboundary mk kl mid)

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
    Branch (g, l, cubes, Leaf n)

  let to_cube_bwv : type n k nk b l.
      k is_singleton -> l Endpoints.len -> (n, k, nk, b) t -> ((n, b) C.t, l) Bwv.t =
   fun k l tube ->
    let One = k in
    let (Branch (_, l', cubes, Leaf _)) = tube in
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

    (* We can convert an hgt of (full, uninstantiated) tubes of constant lengths to a vector. *)
    let rec vec_of_hgt : type b k n bs.
        (b, k, bs) Tlist.conses -> (D.zero, n, n, D.fwd_zero, bs) hgt -> ((D.zero, n, n, b) t, k) Vec.t
        =
     fun bs xs ->
      match (bs, xs) with
      | Nil, [] -> []
      | Cons bs, x :: xs ->
          let xs = vec_of_hgt bs xs in
          x :: xs

    let rec ends : type m k mk g w bs.
        (m, (k, g) D.suc, (mk, g) D.suc, w, bs) hgt -> (mk, w, bs) ends = function
      | [] ->
          let (Wrap l) = Endpoints.wrapped () in
          Ends (l, Nil, [])
      | Branch (_, l1, es, _) :: xs ->
          let (Ends (l2, hs, ess)) = ends xs in
          let Eq = Endpoints.uniq l1 l2 in
          Ends (l2, Cons hs, es :: ess)

    let rec mid : type m k mk g w bs.
        (m, (k, g) D.suc, (mk, g) D.suc, w, bs) hgt -> (m, k, mk, (g, w) cons, bs) hgt = function
      | [] -> []
      | Branch (_, _, _, m) :: xs -> m :: mid xs

    let rec leaf : type n w bs. n D.t -> bs Tlist.t -> (n, D.zero, n, w, bs) hgt =
     fun n bs ->
      match bs with
      | Nil -> []
      | Cons bs -> Leaf n :: leaf n bs

    let rec branch : type m k mk g w bs hs l.
        g D.G.t ->
        l Endpoints.len ->
        (mk, w, bs, hs) C.Heter.hgts ->
        (hs, l) Bwv.Heter.ht ->
        (m, k, mk, (g, w) cons, bs) hgt ->
        (m, (k, g) D.suc, (mk, g) D.suc, w, bs) hgt =
     fun g l hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids ->
          Branch (g, l, ends, mid) :: branch g l hs endss mids
  end

  module Infix = C.Infix

  (* Now the generic traversal.  There are two phases.  The first walks down the instantiated dimensions of the tube, accumulating the word 'a of dimensions decided as Mid so far.  Whenever it takes an End, everything below is an ordinary cube traversal; the second phase performs that traversal while accumulating the *inner* part of the eventual tface's payload strict face, and assembles the complete tface at each leaf using the End data and the Mid-prefix recorded by the first phase.  All the bookkeeping is associativity of word concatenation. *)

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)
    module BwvM = Bwv.Applicatic (M)
    module CM = C.Applicatic (M)

    type ('n, 'k, 'nk, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'cs) C.Heter.hft M.t;
    }

    (* The tube traversal walks only the instantiated dimensions (the tube Branches), accumulating the forwards word 'w of dimensions decided as Mid so far, with pa : (k1, w, k) and pnk : (mk1, w, nk) recording how it sits inside the instantiated and total dimensions.  As soon as we descend an End branch, everything below is an ordinary cube, over which we run the prefixed Cube traversal with 'w as the outer prefix.  The cube's mapper receives a cube face fa together with the bplus (m_fa, w, mb) exhibiting the prefix; we reassemble the full tface with sface_bplus, which prepends the 'w Mids and the one End. *)
    let rec gpmapM_r : type n k1 mk1 w k nk b bs cs.
        (n, k1, mk1) D.plus ->
        (k1, w, k) D.bplus ->
        (mk1, w, nk) D.bplus ->
        w D.fwd ->
        (n, k, nk, (b, bs) cons, cs) pmapperM ->
        (n, k1, mk1, w, (b, bs) cons) Heter.hgt ->
        (* A special Applicative action to take for dimensions that have zero arity *)
        ?ifzero:unit M.t ->
        cs Tlist.t ->
        (n, k1, mk1, w, cs) Heter.hgt M.t =
     fun nk1 pa pnk w g trs ?ifzero cst ->
      match (nk1, trs) with
      | Zero, Leaf n :: _ -> return (Heter.leaf n cst)
      | Suc (nk1', g0), Branch (_, _, _, _) :: _ ->
          let (Ends (l, hs, ends)) = Heter.ends trs in
          let mid = Heter.mid trs in
          let (Hgts newhs) = C.Heter.hgts_of_tlist cst in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.pmapM
                   (fun (e :: brs) ->
                     M.apply
                       (CM.gpmapM_pre w Nil Append_nil Fwsface.Zero
                          {
                            map =
                              (fun fa mb x -> g.map (sface_bplus mb pa pnk fa nk1' g0 e w) x);
                          }
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
                     gpmapM_r nk1' (Append_cons pa) (Append_cons pnk) (Cons (g0, w)) g mid ?ifzero
                       cst)))
          @@ fun (newends, ((), newmid)) -> Heter.branch g0 l newhs newends newmid

    let pmapM : type n k nk b bs cs.
        (n, k, nk, (b, bs) cons, cs) pmapperM ->
        (n, k, nk, D.fwd_zero, (b, bs) cons) Heter.hgt ->
        ?ifzero:unit M.t ->
        cs Tlist.t ->
        (n, k, nk, D.fwd_zero, cs) Heter.hgt M.t =
     fun g trs ?ifzero cst ->
      let (tr :: _) = trs in
      gpmapM_r (plus tr) Append_nil Append_nil Nil g trs ?ifzero cst

    (* And now the more specialized versions. *)

    type ('n, 'k, 'nk, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft -> ('m, 'c) F.t M.t;
    }

    let mmapM : type n k nk b bs c.
        (n, k, nk, (b, bs) cons, c) mmapperM ->
        ?ifzero:unit M.t ->
        (n, k, nk, D.fwd_zero, (b, bs) cons) Heter.hgt ->
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
        (n, k, nk, D.fwd_zero, (b, bs) cons) Heter.hgt ->
        unit M.t =
     fun g ?ifzero xs ->
      M.apply (pmapM { map = (fun fa x -> M.apply (g.it fa x) @@ fun () -> hnil) } xs ?ifzero Nil)
      @@ fun [] -> ()

    (* We also have a monadic builder function *)

    type ('n, 'k, 'nk, 'b) builderM = { build : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'b) F.t M.t }

    (* The tube builder walks only the instantiated dimensions; at each End it builds an ordinary cube via the prefixed Cube builder, reassembling the tface with sface_bplus exactly as in gpmapM_r. *)
    let rec gbuildM_r : type n k1 mk1 w k nk b.
        n D.t ->
        (n, k1, mk1) D.plus ->
        (k1, w, k) D.bplus ->
        (mk1, w, nk) D.bplus ->
        w D.fwd ->
        (n, k, nk, b) builderM ->
        (n, k1, mk1, w, b) gt M.t =
     fun n nk1 pa pnk w g ->
      match nk1 with
      | Zero -> return (Leaf n)
      | Suc (nk1', g0) ->
          let (Wrap l) = Endpoints.wrapped () in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.mapM
                   (fun e ->
                     CM.gbuildM_pre (D.plus_out n nk1') w Nil Append_nil Fwsface.Zero
                       { build = (fun fa mb -> g.build (sface_bplus mb pa pnk fa nk1' g0 e w)) })
                   (Endpoints.indices l))
               (fun () ->
                 gbuildM_r n nk1' (Append_cons pa) (Append_cons pnk) (Cons (g0, w)) g))
          @@ fun (ends, mid) -> Branch (g0, l, ends, mid)

    let buildM : type n k nk b.
        n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) builderM -> (n, k, nk, b) t M.t =
     fun n nk g -> gbuildM_r n nk Append_nil Append_nil Nil g

    (* TODO: Redefine buildM in terms of pbuildM *)

    (* The multi-output builder is to the single builder buildM as the multi-output traversal pmapM is to the single traversal mmapM: it produces a whole hlist of tubes at once, with no inputs.  Like buildM, it has two phases (gpbuildM_cube and gpbuildM_r) mirroring gbuildM_cube and gbuildM_r; like the gpmapM_* family, each one produces an hlist of (cube or tube) gt's rather than a single one. *)

    type ('n, 'k, 'nk, 'bs) pbuilderM = {
      build : 'm. ('m, 'n, 'k, 'nk) tface -> ('m, 'bs) C.Heter.hft M.t;
    }

    (* The multi-output tube builder walks only the instantiated dimensions; at each End it builds a whole hlist of cubes via the prefixed multi-output Cube builder, reassembling the tface with sface_bplus as in gpmapM_r. *)
    let rec gpbuildM_r : type n k1 mk1 w k nk bs.
        n D.t ->
        (n, k1, mk1) D.plus ->
        (k1, w, k) D.bplus ->
        (mk1, w, nk) D.bplus ->
        w D.fwd ->
        (n, k, nk, bs) pbuilderM ->
        bs Tlist.t ->
        (n, k1, mk1, w, bs) Heter.hgt M.t =
     fun n nk1 pa pnk w g bs ->
      match nk1 with
      | Zero -> return (Heter.leaf n bs)
      | Suc (nk1', g0) ->
          let (Wrap l) = Endpoints.wrapped () in
          let (Hgts newhs) = C.Heter.hgts_of_tlist bs in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.pmapM
                   (fun [ e ] ->
                     M.apply
                       (CM.gpbuildM_pre (D.plus_out n nk1') w Nil Append_nil Fwsface.Zero
                          { build = (fun fa mb -> g.build (sface_bplus mb pa pnk fa nk1' g0 e w)) }
                          bs)
                     @@ fun xs -> C.Heter.hlist_of_hgt newhs xs)
                   [ Endpoints.indices l ]
                   (C.Heter.tlist_hgts newhs bs))
               (fun () ->
                 gpbuildM_r n nk1' (Append_cons pa) (Append_cons pnk) (Cons (g0, w)) g bs))
          @@ fun (newends, newmid) -> Heter.branch g0 l newhs newends newmid

    let pbuildM : type n k nk bs.
        n D.t ->
        (n, k, nk) D.plus ->
        (n, k, nk, bs) pbuilderM ->
        bs Tlist.t ->
        (n, k, nk, D.fwd_zero, bs) Heter.hgt M.t =
     fun n nk g bs -> gpbuildM_r n nk Append_nil Append_nil Nil g bs
  end

  module Monadic (M : Monad.Plain) = struct
    module A = Applicative.OfMonad (M)
    include Applicatic (A)
  end

  (* Now we deduce the non-monadic versions *)

  module IdM = Monadic (Monad.Identity)

  let pmap : type n k nk b bs cs.
      (n, k, nk, (b, bs) cons, cs) IdM.pmapperM ->
      (n, k, nk, D.fwd_zero, (b, bs) cons) Heter.hgt ->
      cs Tlist.t ->
      (n, k, nk, D.fwd_zero, cs) Heter.hgt =
   fun g trs cst -> IdM.pmapM g trs cst

  let mmap : type n k nk b bs c.
      (n, k, nk, (b, bs) cons, c) IdM.mmapperM ->
      (n, k, nk, D.fwd_zero, (b, bs) cons) Heter.hgt ->
      (n, k, nk, c) t =
   fun g xs -> IdM.mmapM g xs

  let miter : type n k nk b bs.
      (n, k, nk, (b, bs) cons) IdM.miteratorM -> (n, k, nk, D.fwd_zero, (b, bs) cons) Heter.hgt -> unit
      =
   fun g xs -> IdM.miterM g xs

  let build : type n k nk b.
      n D.t -> (n, k, nk) D.plus -> (n, k, nk, b) IdM.builderM -> (n, k, nk, b) t =
   fun n nk g -> IdM.buildM n nk g

  let pbuild : type n k nk bs.
      n D.t ->
      (n, k, nk) D.plus ->
      (n, k, nk, bs) IdM.pbuilderM ->
      bs Tlist.t ->
      (n, k, nk, D.fwd_zero, bs) Heter.hgt =
   fun n nk g bs -> IdM.pbuildM n nk g bs
end

module TubeOf = struct
  include Tube (FamOf)

  (* We can lift and lower a tube too *)

  let rec glift : type m k mk w1 n2 w12 b.
      n2 D.fwd -> (w1, n2, w12) D.fplus -> (m, k, mk, w1, b) gt -> (m, k, mk, w12, b) gt =
   fun n2 fp tr ->
    match tr with
    | Leaf m -> Leaf m
    | Branch (g, l, ends, mid) ->
        Branch (g, l, Bwv.map (fun t -> CubeOf.lift n2 fp t) ends, glift n2 (Cons fp) mid)

  let rec glower : type m k mk w1 n2 w12 b.
      (m, k, mk, w12, b) gt -> (w1, n2, w12) D.fplus -> (m, k, mk, w1, b) gt =
   fun tr fp ->
    match tr with
    | Leaf m -> Leaf m
    | Branch (g, l, ends, mid) ->
        Branch (g, l, Bwv.map (fun t -> CubeOf.lower t fp) ends, glower mid (Cons fp))

  (* We can fill in the missing pieces of a tube with a cube, yielding a cube.  The witness (l, w, lw) records how the decided word of the filling cube extends that of the tube. *)

  let rec gplus_gcube : type m l ml w lw b.
      (l, w, lw) D.bfplus -> (m, l, ml, w, b) gt -> (m, lw, b) C.gt -> (ml, w, b) C.gt =
   fun lw tl tm ->
    match tl with
    | Leaf _ ->
        let Zero = lw in
        tm
    | Branch (g, l, ends, mid) ->
        let (Suc lw') = lw in
        Branch (g, l, ends, gplus_gcube lw' mid tm)

  let plus_cube : type m l ml b. (m, l, ml, b) t -> (m, b) C.t -> (ml, b) C.t =
   fun tl tm ->
    let l_run = D.plus_right (gplus tl) in
    let (Bfplus (lw, bfp)) = D.bfplus l_run D.fwd_zero in
    gplus_gcube bfp tl (CubeOf.lift lw Nil tm)

  (* Or we can fill in some of those missing pieces with a tube instead, yielding another tube.  The witness (l, w, lw) records how the decided word of the inner tube extends that of the outer one. *)

  let rec gplus_gtube : type m k mk l kl mkl w lw b.
      (k, l, kl) D.plus ->
      (l, w, lw) D.bfplus ->
      (mk, l, mkl, w, b) gt ->
      (m, k, mk, lw, b) gt ->
      (m, kl, mkl, w, b) gt =
   fun kl lw tl tk ->
    match (kl, tl) with
    | Zero, Leaf _ ->
        let Zero = lw in
        tk
    | Suc (kl, _), Branch (g', l, ends, mid) ->
        let (Suc lw') = lw in
        Branch (g', l, ends, gplus_gtube kl lw' mid tk)

  let plus_tube : type m k mk l kl mkl b.
      (k, l, kl) D.plus -> (mk, l, mkl, b) t -> (m, k, mk, b) t -> (m, kl, mkl, b) t =
   fun kl tl tk ->
    let l_run = D.plus_right kl in
    let (Bfplus (lw, bfp)) = D.bfplus l_run D.fwd_zero in
    gplus_gtube kl bfp tl (glift lw Nil tk)

  (* We can also pick out a lower-dimensional part around the middle of a tube, as well as the outer tube around it.  The witness (l, w, lw) records the decided word of the inner part relative to the outer. *)

  let rec gsplit : type m k mk l kl mkl w lw b.
      (m, k, mk) D.plus ->
      (k, l, kl) D.plus ->
      (l, w, lw) D.bfplus ->
      (m, kl, mkl, w, b) gt ->
      (m, k, mk, lw, b) gt * (mk, l, mkl, w, b) gt =
   fun mk kl lw tr ->
    match (kl, tr) with
    | Zero, _ ->
        let Eq = D.plus_uniq mk (gplus tr) in
        let Zero = lw in
        (tr, Leaf (D.plus_out (guninst tr) mk))
    | Suc (kl, _), Branch (g', l, ends, mid) ->
        let (Suc lw') = lw in
        let middle, outer = gsplit mk kl lw' mid in
        (middle, Branch (g', l, ends, outer))

  let split : type m k mk l kl mkl b.
      (m, k, mk) D.plus ->
      (k, l, kl) D.plus ->
      (m, kl, mkl, b) t ->
      (m, k, mk, b) t * (mk, l, mkl, b) t =
   fun mk kl tr ->
    let l_run = D.plus_right kl in
    let (Bfplus (_, bfp)) = D.bfplus l_run D.fwd_zero in
    let middle, outer = gsplit mk kl bfp tr in
    (glower middle Nil, outer)

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
