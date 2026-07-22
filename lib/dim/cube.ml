open Util
open Signatures
open Tlist
open Hlist
open Sface
module Fw = Fwsface

(* A cube of dimension 'm is a data structure that records one object for each strict face of 'm, in a ternary tree so that they can be accessed randomly by strict face as well as sequentially.  We allow the *type* of each object to depend on the *domain* of the strict face that indexes it, by parametrizing the notion with a functor.  We also allow an extra dependence on some additional type, so that an individual functor application can be parametric. *)

module Cube (F : Fam2) = struct
  (* An ('m, 'w, 'b) gt is a tree of uniform height 'm (a dimension word), whose interior nodes branch on the *outermost* remaining generator, with endpoint branches and one special "mid" branch.  The second index 'w is the *forwards* word of generators already *decided* to be kept (i.e. taken as Mid) on the path leading down to this subtree.  The intrinsic dimensions are processed from the outside in, and a newly decided generator is consed onto the *inner* (head) end of 'w; since this is structural (a [cons]), the Branch stores no witness for it.  A leaf reconciles its accumulated forwards word 'w with the actual backwards dimension 'r via a bplus onto the empty word, and is labeled by an element of F('r, 'b).  All the index bookkeeping in traversals is then either a [cons] or a single [Append_cons], valid for any number of generators. *)
  type (_, _, _) gt =
    | Leaf : (D.zero, 'w, 'r) D.bplus * ('r, 'b) F.t -> (D.zero, 'w, 'b) gt
    | Branch :
        'g D.G.t * 'l Endpoints.len * (('m, 'w, 'b) gt, 'l) Bwv.t * ('m, ('g, 'w) cons, 'b) gt
        -> (('m, 'g) D.suc, 'w, 'b) gt

  (* A cube of dimension 'n is a gt of height 'n with nothing yet decided. *)
  type ('n, 'b) t = ('n, D.fwd_zero, 'b) gt

  (* This two-step data definition means that all the functions that act on them must also be defined in terms of a gt version.  However, in the interface we expose only the t versions. *)

  (* For instance, we can compute the dimension of a cube. *)
  let rec gdim : type m w b. (m, w, b) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (g, _, _, br) -> D.suc (gdim br) g

  let dim : type n b. (n, b) t -> n D.t = fun tr -> gdim tr

  (* A cube of dimension zero is just an element. *)

  let singleton : type b. (D.zero, b) F.t -> (D.zero, b) t = fun x -> Leaf (Append_nil, x)

  (* A strict face is an index into a face tree.  We walk the gt and the sface in lockstep: the sface's outermost constructor corresponds to the root branch.  The carried plus relation (j, w, p) records that the value found will live at p = j + w, where j is the part of the sface's domain not yet walked past and w is the decided word so far; at each Mid step the newly decided generator moves from j to w, witnessed by the plus stored in the Branch together with associativity. *)

  let rec gfind : type m w b j p. (m, w, b) gt -> (j, m) sface -> (j, w, p) D.bplus -> (p, b) F.t =
   fun tr d jw ->
    match (tr, d) with
    | Leaf (bp, x), Zero ->
        let Eq = D.bplus_uniq bp jw in
        x
    | Branch (_, l1, ends, _), End (d, _, (l2, e)) ->
        let Eq = Endpoints.uniq l1 l2 in
        gfind (Bwv.nth e ends) d jw
    | Branch (_, _, _, mid), Mid (d, _) -> gfind mid d (Append_cons jw)

  let find : type n k b. (n, b) t -> (k, n) sface -> (k, b) F.t = fun tr d -> gfind tr d Append_nil

  let rec gfind_top : type m w p b. (m, w, b) gt -> (m, w, p) D.bplus -> (p, b) F.t =
   fun tr mw ->
    match tr with
    | Leaf (bp, x) ->
        let Eq = D.bplus_uniq bp mw in
        x
    | Branch (_, _, _, br) -> gfind_top br (Append_cons mw)

  let find_top : type n b. (n, b) t -> (n, b) F.t = fun tr -> gfind_top tr Append_nil

  (* Heterogeneous lists and multimaps, which take the current face as input everywhere in addition to the values in the data structure.  We use the technique of heteregeneous generic traversal, which is a much more significant win here in terms of coding because we only have to descend into gt's once, and all the other operations can be derived from the simpler t version. *)

  module Heter = struct
    (* An hlist of elements of F.t, with the first parameter fixed but the second varying along the list. *)
    type (_, _) hft =
      | [] : ('n, nil) hft
      | ( :: ) : ('n, 'x) F.t * ('n, 'xs) hft -> ('n, ('x, 'xs) cons) hft

    (* An hlist of gt's, with the first two parameters (dimensions) fixed but the third varying along the list.  *)
    type (_, _, _) hgt =
      | [] : ('m, 'w, nil) hgt
      | ( :: ) : ('m, 'w, 'x) gt * ('m, 'w, 'xs) hgt -> ('m, 'w, ('x, 'xs) cons) hgt

    (* A relational function constructing, for any tlist of value types, the corresponding tlist of gt types.  *)
    type (_, _, _, _) hgts =
      | Nil : ('m, 'w, nil, nil) hgts
      | Cons : ('m, 'w, 'xs, 'ys) hgts -> ('m, 'w, ('x, 'xs) cons, (('m, 'w, 'x) gt, 'ys) cons) hgts

    (* The next two functions are inverse isomorphisms. *)
    let rec hlist_of_hgt : type m w xs ys. (m, w, xs, ys) hgts -> (m, w, xs) hgt -> ys hlist =
     fun hs xs ->
      match (hs, xs) with
      | Nil, [] -> []
      | Cons hs, x :: xs -> x :: hlist_of_hgt hs xs

    let rec hgt_of_hlist : type m w xs ys. (m, w, xs, ys) hgts -> ys hlist -> (m, w, xs) hgt =
     fun hs xs ->
      match (hs, xs) with
      | Nil, [] -> []
      | Cons hs, x :: xs -> x :: hgt_of_hlist hs xs

    (* We can also make an hft of constant types from a vector of the right length. *)
    let rec hft_of_vec : type b k n bs.
        (b, k, bs) Tlist.conses -> ((n, b) F.t, k) Vec.t -> (n, bs) hft =
     fun bs xs ->
      match (bs, xs) with
      | Nil, [] -> []
      | Cons bs, x :: xs ->
          let xs = hft_of_vec bs xs in
          x :: xs

    (* hgts preserves validity of tlists. *)
    let rec tlist_hgts : type m w xs ys. (m, w, xs, ys) hgts -> xs Tlist.t -> ys Tlist.t =
     fun hs xs ->
      match (hs, xs) with
      | Nil, Nil -> Nil
      | Cons hs, Cons xs -> Cons (tlist_hgts hs xs)

    (* And any tlist of value types has some corresponding list of gts. *)
    type (_, _, _) has_hgts = Hgts : ('m, 'w, 'xs, 'xss) hgts -> ('m, 'w, 'xs) has_hgts

    let rec hgts_of_tlist : type m w xs. xs Tlist.t -> (m, w, xs) has_hgts = function
      | Nil -> Hgts Nil
      | Cons xs ->
          let (Hgts xss) = hgts_of_tlist xs in
          Hgts (Cons xss)

    (* Extract the pieces of an hlist of gt's. *)
    let rec lab : type w r bs. (D.zero, w, r) D.bplus -> (D.zero, w, bs) hgt -> (r, bs) hft =
     fun bp -> function
      | [] -> []
      | Leaf (bp', x) :: xs ->
          let Eq = D.bplus_uniq bp' bp in
          x :: lab bp xs

    type (_, _, _) ends =
      | Ends :
          'l Endpoints.len * ('m, 'w, 'bs, 'hs) hgts * ('hs, 'l) Bwv.Heter.ht
          -> ('m, 'w, 'bs) ends

    let rec ends : type m g w bs. ((m, g) D.suc, w, bs) hgt -> (m, w, bs) ends = function
      | [] ->
          let (Wrap l) = Endpoints.wrapped () in
          Ends (l, Nil, [])
      | Branch (_, l1, es, _) :: xs ->
          let (Ends (l2, hs, ess)) = ends xs in
          let Eq = Endpoints.uniq l1 l2 in
          Ends (l2, Cons hs, es :: ess)

    let rec mid : type m g w bs. ((m, g) D.suc, w, bs) hgt -> (m, (g, w) cons, bs) hgt = function
      | [] -> []
      | Branch (_, _, _, m) :: xs -> m :: mid xs

    (* Construct an hlist of gt's as leaves or branches.  *)
    let rec leaf : type w r bs. (D.zero, w, r) D.bplus -> (r, bs) hft -> (D.zero, w, bs) hgt =
     fun bp -> function
      | [] -> []
      | x :: xs -> Leaf (bp, x) :: leaf bp xs

    let rec branch : type l g m w bs hs.
        g D.G.t ->
        l Endpoints.len ->
        (m, w, bs, hs) hgts ->
        (hs, l) Bwv.Heter.ht ->
        (m, (g, w) cons, bs) hgt ->
        ((m, g) D.suc, w, bs) hgt =
     fun g l hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids -> Branch (g, l, ends, mid) :: branch g l hs endss mids
  end

  (* The function that we apply on a generic traversal must be polymorphic over the domain dimension of the face, so we wrap it in a record. *)
  type ('n, 'bs, 'cs) pmapper = {
    map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'cs) Heter.hft;
  }

  (* A "prefixed" mapper additionally receives a bplus ('m, 'p, 'mb) exhibiting an outer prefix 'p appended to the face domain 'm; its input and output hfts live at the prefixed dimension 'mb.  This is exactly what a Tube needs when it descends into an End branch and hands off to the Cube traversal: 'p is the word of Mid dimensions decided in the Tube above, and the cube's leaf values live at (cube face) + 'p. *)
  type ('n, 'p, 'bs, 'cs) pmapper_pre = {
    map :
      'm 'mb.
      ('m, 'n) sface -> ('m, 'p, 'mb) D.bplus -> ('mb, 'bs) Heter.hft -> ('mb, 'cs) Heter.hft;
  }

  (* The generic prefixed traversal.  'own is the decided word for the cube's own descent (the fwsface domain), 'p the fixed outer prefix, and 'w = 'own + 'p the gt's decided-word index, witnessed by the fplus 'fp.  'cf is the consumed codomain with 'mc : ('m, 'cf, 'n) bplus.  At each Branch the newly consumed generator is consed onto the fwsface and the bplus by Append_cons; a Mid additionally grows 'own (and 'fp). *)
  let rec gpmap_pre : type m own p w cf n b bs cs.
      p D.fwd ->
      (own, p, w) D.fplus ->
      (m, cf, n) D.bplus ->
      (own, cf) Fw.fwsface ->
      (n, p, (b, bs) cons, cs) pmapper_pre ->
      (m, w, (b, bs) cons) Heter.hgt ->
      cs Tlist.t ->
      (m, w, cs) Heter.hgt =
   fun p fp mc d g trs cst ->
    match trs with
    | Leaf _ :: _ ->
        let (Bplus dbp) = D.bplus (Fw.dom_fwsface d) in
        let (Bplus mb) = D.bplus p in
        let dbp_full = D.bplus_bplus dbp mb fp in
        let x = g.map (Fw.sface_of_fw dbp mc d) mb (Heter.lab dbp_full trs) in
        Heter.leaf dbp_full x
    | Branch (g0, _, _, _) :: _ ->
        let (Ends (l, hs, ends)) = Heter.ends trs in
        let mid = Heter.mid trs in
        let (Hgts newhs) = Heter.hgts_of_tlist cst in
        let newends =
          Bwv.pmap
            (fun (e :: brs) ->
              let xs =
                gpmap_pre p fp (Append_cons mc)
                  (Fw.End (g0, e, d))
                  g (Heter.hgt_of_hlist hs brs) cst in
              Heter.hlist_of_hgt newhs xs)
            (Endpoints.indices l :: ends) (Heter.tlist_hgts newhs cst) in
        let newmid = gpmap_pre p (Cons fp) (Append_cons mc) (Fw.Mid (g0, d)) g mid cst in
        Heter.branch g0 l newhs newends newmid

  (* And the actual one for a t, which we can henceforth restrict our attention to.  It is the empty-prefix special case, where the bplus handed to the mapper is trivial and the hfts live at the face domain itself. *)
  let pmap : type n b bs cs.
      (n, (b, bs) cons, cs) pmapper ->
      (n, D.fwd_zero, (b, bs) cons) Heter.hgt ->
      cs Tlist.t ->
      (n, D.fwd_zero, cs) Heter.hgt =
   fun g xs cs ->
    let g' : (n, nil, (b, bs) cons, cs) pmapper_pre =
      {
        map =
          (fun (type m mb)
            (fa : (m, n) sface)
            (mb : (m, nil, mb) D.bplus)
            (x : (mb, (b, bs) cons) Heter.hft)
            :
            (mb, cs) Heter.hft
          ->
            match mb with
            | Append_nil -> g.map fa x);
      } in
    gpmap_pre Nil Nil Append_nil Fw.Zero g' xs cs

  type ('n, 'bs, 'c) mmapper = { map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'c) F.t }

  let mmap : type n b bs c.
      (n, (b, bs) cons, c) mmapper -> (n, D.fwd_zero, (b, bs) cons) Heter.hgt -> (n, c) t =
   fun g xs ->
    let [ ys ] =
      pmap
        {
          map =
            (fun fa x ->
              let y = g.map fa x in
              [ y ]);
        }
        xs (Cons Nil) in
    ys

  type ('n, 'bs) miterator = { it : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> unit }

  let miter : type n b bs.
      (n, (b, bs) cons) miterator -> (n, D.fwd_zero, (b, bs) cons) Heter.hgt -> unit =
   fun g xs ->
    let [] =
      pmap
        {
          map =
            (fun fa x ->
              g.it fa x;
              []);
        }
        xs Nil in
    ()

  (* A binary iterator over two cubes of the *same* functor F (but possibly different parameters b1, b2).  It is defined in terms of the generic variadic miter, but crucially the existential-opening of the element family (e.g. BindFam) happens in the *caller's* it2, checked against this plain fixed-arity-2 signature, NOT inside the rank-2 field passed to miter (where x and y stay abstract and are merely forwarded).  So miter is only ever instantiated at an abstract 2-element Tlist with no existential-opening in the rank-2 field, which is cheap.  Calling miter [ c1; c2 ] *directly* on two GADT-family cubes, opening the existentials in its rank-2 field at the concrete Tlist, is what causes a catastrophic type-inference blowup (see the Pi arm of equal_head in core/equal.ml); this wrapper keeps the two ingredients apart. *)
  type ('n, 'b1, 'b2) miterator2 = {
    it2 : 'm. ('m, 'n) sface -> ('m, 'b1) F.t -> ('m, 'b2) F.t -> unit;
  }

  let miter2 : type n b1 b2. (n, b1, b2) miterator2 -> (n, b1) t -> (n, b2) t -> unit =
   fun g xs ys -> miter { it = (fun fa [ x; y ] -> g.it2 fa x y) } [ xs; ys ]

  (* The builder function isn't quite a special case of the generic traversal, since it needs to maintain different information when constructing a cube from scratch. *)

  type ('n, 'b) builder = { build : 'm. ('m, 'n) sface -> ('m, 'b) F.t }

  (* The prefixed builder, exactly as gpmap_pre is to gpmap: the callback receives the outer-prefix bplus, and builds a value at the prefixed dimension. *)
  type ('n, 'p, 'b) builder_pre = {
    build : 'm 'mb. ('m, 'n) sface -> ('m, 'p, 'mb) D.bplus -> ('mb, 'b) F.t;
  }

  let rec gbuild_pre : type m own p w cf n b.
      m D.t ->
      p D.fwd ->
      (own, p, w) D.fplus ->
      (m, cf, n) D.bplus ->
      (own, cf) Fw.fwsface ->
      (n, p, b) builder_pre ->
      (m, w, b) gt =
   fun m p fp mc d g ->
    match m with
    | Word Zero ->
        let (Bplus dbp) = D.bplus (Fw.dom_fwsface d) in
        let (Bplus mb) = D.bplus p in
        let dbp_full = D.bplus_bplus dbp mb fp in
        let x = g.build (Fw.sface_of_fw dbp mc d) mb in
        Leaf (dbp_full, x)
    | Word (Suc (m1, g0)) ->
        let (Wrap l) = Endpoints.wrapped () in
        let ends =
          Bwv.map
            (fun e -> gbuild_pre (Word m1) p fp (Append_cons mc) (Fw.End (g0, e, d)) g)
            (Endpoints.indices l) in
        let mid = gbuild_pre (Word m1) p (Cons fp) (Append_cons mc) (Fw.Mid (g0, d)) g in
        Branch (g0, l, ends, mid)

  let build : type n b. n D.t -> (n, b) builder -> (n, b) t =
   fun n g ->
    let g' : (n, nil, b) builder_pre =
      {
        build =
          (fun (type m mb) (fa : (m, n) sface) (mb : (m, nil, mb) D.bplus) : (mb, b) F.t ->
            match mb with
            | Append_nil -> g.build fa);
      } in
    gbuild_pre n Nil Nil Append_nil Fw.Zero g'

  (* TODO: Redefine build in terms of pbuild *)

  (* The multi-output builder is to the single builder build as the multi-output traversal pmap is to the single traversal mmap: it produces a whole hlist of cubes at once, with no inputs.  It is thus gbuild made plural, threading the same forwards decided word (see gbuild and gpmap) but producing an hgt of gt's rather than a single one. *)

  type ('n, 'bs) pbuilder = { build : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft }

  type ('n, 'p, 'bs) pbuilder_pre = {
    build : 'm 'mb. ('m, 'n) sface -> ('m, 'p, 'mb) D.bplus -> ('mb, 'bs) Heter.hft;
  }

  let rec gpbuild_pre : type m own p w cf n bs.
      m D.t ->
      p D.fwd ->
      (own, p, w) D.fplus ->
      (m, cf, n) D.bplus ->
      (own, cf) Fw.fwsface ->
      (n, p, bs) pbuilder_pre ->
      bs Tlist.t ->
      (m, w, bs) Heter.hgt =
   fun m p fp mc d g bs ->
    match m with
    | Word Zero ->
        let (Bplus dbp) = D.bplus (Fw.dom_fwsface d) in
        let (Bplus mb) = D.bplus p in
        let dbp_full = D.bplus_bplus dbp mb fp in
        let x = g.build (Fw.sface_of_fw dbp mc d) mb in
        Heter.leaf dbp_full x
    | Word (Suc (m1, g0)) ->
        let (Wrap l) = Endpoints.wrapped () in
        let (Hgts newhs) = Heter.hgts_of_tlist bs in
        let newends =
          Bwv.pmap
            (fun [ e ] ->
              let xs = gpbuild_pre (Word m1) p fp (Append_cons mc) (Fw.End (g0, e, d)) g bs in
              Heter.hlist_of_hgt newhs xs)
            [ Endpoints.indices l ]
            (Heter.tlist_hgts newhs bs) in
        let newmid = gpbuild_pre (Word m1) p (Cons fp) (Append_cons mc) (Fw.Mid (g0, d)) g bs in
        Heter.branch g0 l newhs newends newmid

  let pbuild : type n bs. n D.t -> (n, bs) pbuilder -> bs Tlist.t -> (n, D.fwd_zero, bs) Heter.hgt =
   fun n g bs ->
    let g' : (n, nil, bs) pbuilder_pre =
      {
        build =
          (fun (type m mb) (fa : (m, n) sface) (mb : (m, nil, mb) D.bplus) : (mb, bs) Heter.hft ->
            match mb with
            | Append_nil -> g.build fa);
      } in
    gpbuild_pre n Nil Nil Append_nil Fw.Zero g' bs

  (* A "subcube" of a cube of dimension n, determined by a face of n with dimension k, is the cube of dimension k consisting of the elements indexed by faces that factor through the given one. *)
  let subcube : type m n b. (m, n) sface -> (n, b) t -> (m, b) t =
   fun fa tr -> build (dom_sface fa) { build = (fun fb -> find tr (comp_sface fa fb)) }
end

(* In the vast majority of cases, the second type parameter 'b in a Fam can just *be* the type of the elements.  The only case when this doesn't work is when the type has to also depend on the dimension 'a. *)
module FamOf = struct
  type ('a, 'b) t = 'b
end

module CubeOf = struct
  include Cube (FamOf)

  (* In this special case, we can change the decided-word index fairly arbitrarily, although it takes a bit of work to convince OCaml.  (Of course, semantically these are identity functions.)  Lifting extends the forwards decided word on the outside (the tail), i.e. by a forwards concatenation ['n2] appended after ['w1]; only the leaves' bplus witnesses need transporting, which is again pure associativity. *)

  let rec lift : type m w1 n2 w12 b.
      n2 D.fwd -> (w1, n2, w12) D.fplus -> (m, w1, b) gt -> (m, w12, b) gt =
   fun n2 fp tr ->
    match tr with
    | Leaf (bp, x) ->
        let (Bplus ext) = D.bplus n2 in
        Leaf (D.bplus_bplus bp ext fp, x)
    | Branch (g, l, ends, mid) ->
        Branch (g, l, Bwv.map (fun t -> lift n2 fp t) ends, lift n2 (Cons fp) mid)

  let rec lower : type m w1 n2 w12 b. (m, w12, b) gt -> (w1, n2, w12) D.fplus -> (m, w1, b) gt =
   fun tr fp ->
    match tr with
    | Leaf (bp, x) ->
        let (Bplus bp') = D.unbplus_bplus bp fp in
        Leaf (bp', x)
    | Branch (g, l, ends, mid) ->
        Branch (g, l, Bwv.map (fun t -> lower t fp) ends, lower mid (Cons fp))
end
