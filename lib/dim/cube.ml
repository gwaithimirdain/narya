open Util
open Signatures
open Tlist
open Hlist
open Sface

(* A cube of dimension 'm is a data structure that records one object for each strict face of 'm, in a ternary tree so that they can be accessed randomly by strict face as well as sequentially.  We allow the *type* of each object to depend on the *domain* of the strict face that indexes it, by parametrizing the notion with a functor.  We also allow an extra dependence on some additional type, so that an individual functor application can be parametric. *)

module Cube (F : Fam2) = struct
  (* An ('m, 'w, 'b) gt is a tree of uniform height 'm (a dimension word), whose interior nodes branch on the *outermost* remaining generator, with endpoint branches and one special "mid" branch.  The second index 'w records the word of generators already *decided* to be kept (i.e. taken as Mid) on the path leading down to this subtree; since the descent processes generators from the outside in, earlier decisions appear as outer generators of 'w.  A leaf is labeled by an element of F('w, 'b) where 'w is the decided word accumulated along the path to it.  When a Branch keeps its generator 'g (the mid branch), that generator is added at the *inner* end of the decided word; the Branch stores the witness for this as a [((zero,'g) suc, 'w, 'gw) D.plus].  All the index bookkeeping in traversals is then pure associativity of word concatenation, which is valid for any number of generators. *)
  type (_, _, _) gt =
    | Leaf : ('w, 'b) F.t -> (D.zero, 'w, 'b) gt
    | Branch :
        'g D.G.t
        * ((D.zero, 'g) D.suc, 'w, 'gw) D.plus
        * 'l Endpoints.len
        * (('m, 'w, 'b) gt, 'l) Bwv.t
        * ('m, 'gw, 'b) gt
        -> (('m, 'g) D.suc, 'w, 'b) gt

  (* A cube of dimension 'n is a gt of height 'n with nothing yet decided. *)
  type ('n, 'b) t = ('n, D.zero, 'b) gt

  (* This two-step data definition means that all the functions that act on them must also be defined in terms of a gt version.  However, in the interface we expose only the t versions. *)

  (* For instance, we can compute the dimension of a cube. *)
  let rec gdim : type m w b. (m, w, b) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (g, _, _, _, br) -> D.suc (gdim br) g

  let dim : type n b. (n, b) t -> n D.t = fun tr -> gdim tr

  (* A cube of dimension zero is just an element. *)

  let singleton : type b. (D.zero, b) F.t -> (D.zero, b) t = fun x -> Leaf x

  (* A strict face is an index into a face tree.  We walk the gt and the sface in lockstep: the sface's outermost constructor corresponds to the root branch.  The carried plus relation (j, w, p) records that the value found will live at p = j + w, where j is the part of the sface's domain not yet walked past and w is the decided word so far; at each Mid step the newly decided generator moves from j to w, witnessed by the plus stored in the Branch together with associativity. *)

  let rec gfind : type m w b j p. (m, w, b) gt -> (j, m) sface -> (j, w, p) D.plus -> (p, b) F.t =
   fun tr d jw ->
    match (tr, d) with
    | Leaf x, Zero ->
        let Eq = D.zero_plus_uniq jw in
        x
    | Branch (_, _, l1, ends, _), End (d, _, (l2, e)) ->
        let Eq = Endpoints.uniq l1 l2 in
        gfind (Bwv.nth e ends) d jw
    | Branch (_, pw, _, _, mid), Mid (d, g) -> gfind mid d (D.plus_assocr (Suc (Zero, g)) pw jw)

  let find : type n k b. (n, b) t -> (k, n) sface -> (k, b) F.t = fun tr d -> gfind tr d Zero

  let rec gfind_top : type m w p b. (m, w, b) gt -> (m, w, p) D.plus -> (p, b) F.t =
   fun tr mw ->
    match tr with
    | Leaf x ->
        let Eq = D.zero_plus_uniq mw in
        x
    | Branch (g, pw, _, _, br) -> gfind_top br (D.plus_assocr (Suc (Zero, g)) pw mw)

  let find_top : type n b. (n, b) t -> (n, b) F.t = fun tr -> gfind_top tr Zero

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
    let rec lab : type w bs. (D.zero, w, bs) hgt -> (w, bs) hft = function
      | [] -> []
      | Leaf x :: xs -> x :: lab xs

    type (_, _, _) ends =
      | Ends :
          'l Endpoints.len * ('m, 'w, 'bs, 'hs) hgts * ('hs, 'l) Bwv.Heter.ht
          -> ('m, 'w, 'bs) ends

    let rec ends : type m g w bs. ((m, g) D.suc, w, bs) hgt -> (m, w, bs) ends = function
      | [] ->
          let (Wrap l) = Endpoints.wrapped () in
          Ends (l, Nil, [])
      | Branch (_, _, l1, es, _) :: xs ->
          let (Ends (l2, hs, ess)) = ends xs in
          let Eq = Endpoints.uniq l1 l2 in
          Ends (l2, Cons hs, es :: ess)

    let rec mid : type m g w gw bs.
        ((D.zero, g) D.suc, w, gw) D.plus -> ((m, g) D.suc, w, bs) hgt -> (m, gw, bs) hgt =
     fun pw xss ->
      match xss with
      | [] -> []
      | Branch (_, pw', _, _, m) :: xs ->
          let Eq = D.plus_uniq pw pw' in
          m :: mid pw xs

    (* Construct an hlist of gt's as leaves or branches.  *)
    let rec leaf : type w bs. (w, bs) hft -> (D.zero, w, bs) hgt = function
      | [] -> []
      | x :: xs -> Leaf x :: leaf xs

    let rec branch : type l g m w gw bs hs.
        g D.G.t ->
        ((D.zero, g) D.suc, w, gw) D.plus ->
        l Endpoints.len ->
        (m, w, bs, hs) hgts ->
        (hs, l) Bwv.Heter.ht ->
        (m, gw, bs) hgt ->
        ((m, g) D.suc, w, bs) hgt =
     fun g pw l hs endss mids ->
      match (hs, endss, mids) with
      | Nil, [], [] -> []
      | Cons hs, ends :: endss, mid :: mids ->
          Branch (g, pw, l, ends, mid) :: branch g pw l hs endss mids
  end

  (* OCaml can't always tell from context what [x ; xs] should be; in particular it often fails to notice hfts.  So we also give a different syntax that is unambiguous.  *)
  module Infix = struct
    let hnil : type n. (n, nil) Heter.hft = []

    let ( @: ) : type n x xs. (n, x) F.t -> (n, xs) Heter.hft -> (n, (x, xs) cons) Heter.hft =
     fun x xs -> x :: xs
  end

  open Infix

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)
    module BwvM = Bwv.Applicatic (M)

    (* The function that we apply on a generic traversal must be polymorphic over the domain dimension of the face, so we wrap it in a record. *)
    type ('n, 'bs, 'cs) pmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'cs) Heter.hft M.t;
    }

    (* The generic traversal carries the partial strict face accumulated so far: 'w is the decided word (the gt index) and 'c is the word of dimensions already consumed by the descent (the outer part of the total dimension 'n, witnessed by the (m, c, n) plus where m is the remaining height).  At each Branch the newly consumed generator is pushed at the *inner* end of the partial face by sface_plus_sface, and the plus relations are transported by associativity. *)
    let rec gpmapM : type m w c n b bs cs.
        (m, c, n) D.plus ->
        (w, c) sface ->
        (n, (b, bs) cons, cs) pmapperM ->
        (m, w, (b, bs) cons) Heter.hgt ->
        cs Tlist.t ->
        (m, w, cs) Heter.hgt M.t =
     fun mc f g trs cst ->
      match trs with
      | Leaf _ :: _ ->
          let Eq = D.zero_plus_uniq mc in
          M.apply (g.map f (Heter.lab trs)) @@ fun x -> Heter.leaf x
      | Branch (g0, pw, _, _, _) :: _ ->
          let (Ends (l, hs, ends)) = Heter.ends trs in
          let mid = Heter.mid pw trs in
          let (Hgts newhs) = Heter.hgts_of_tlist cst in
          let (Plus plc) = D.plus (cod_sface f) in
          let pwd = D.plus_assocr (Suc (Zero, g0)) plc mc in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.pmapM
                   (fun (e :: brs) ->
                     M.apply
                       (gpmapM pwd
                          (sface_plus_sface (End (Zero, g0, e)) plc (D.zero_plus (dom_sface f)) f)
                          g (Heter.hgt_of_hlist hs brs) cst)
                     @@ fun xs -> Heter.hlist_of_hgt newhs xs)
                   (Endpoints.indices l :: ends) (Heter.tlist_hgts newhs cst))
               (fun () -> gpmapM pwd (sface_plus_sface (Mid (Zero, g0)) plc pw f) g mid cst))
          @@ fun (newends, newmid) -> Heter.branch g0 pw l newhs newends newmid

    (* And the actual one for a t, which we can henceforth restrict our attention to. *)
    let pmapM : type n b bs cs.
        (n, (b, bs) cons, cs) pmapperM ->
        (n, D.zero, (b, bs) cons) Heter.hgt ->
        cs Tlist.t ->
        (n, D.zero, cs) Heter.hgt M.t =
     fun g xs cs -> gpmapM Zero Zero g xs cs

    type ('n, 'bs, 'c) mmapperM = {
      map : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> ('m, 'c) F.t M.t;
    }

    let mmapM : type n b bs c.
        (n, (b, bs) cons, c) mmapperM -> (n, D.zero, (b, bs) cons) Heter.hgt -> (n, c) t M.t =
     fun g xs ->
      M.apply
        (pmapM
           {
             map =
               (fun fa x ->
                 M.apply (g.map fa x) @@ fun y ->
                 (* Apparently writing [y] is insufficiently polymorphic *)
                 y @: []);
           }
           xs (Cons Nil))
      @@ fun [ ys ] -> ys

    type ('n, 'bs) miteratorM = { it : 'm. ('m, 'n) sface -> ('m, 'bs) Heter.hft -> unit M.t }

    let miterM : type n b bs.
        (n, (b, bs) cons) miteratorM -> (n, D.zero, (b, bs) cons) Heter.hgt -> unit M.t =
     fun g xs ->
      M.apply (pmapM { map = (fun fa x -> M.apply (g.it fa x) @@ fun () -> hnil) } xs Nil)
      @@ fun [] -> ()

    (* The builder function isn't quite a special case of the generic traversal, since it needs to maintain different information when constructing a cube from scratch. *)

    type ('n, 'b) builderM = { build : 'm. ('m, 'n) sface -> ('m, 'b) F.t M.t }

    let rec gbuildM : type m w c n b.
        m D.t -> (m, c, n) D.plus -> (w, c) sface -> (n, b) builderM -> (m, w, b) gt M.t =
     fun m mc f g ->
      match m with
      | Word Zero ->
          let Eq = D.zero_plus_uniq mc in
          M.apply (g.build f) @@ fun x -> Leaf x
      | Word (Suc (m1, g0)) ->
          let (Plus plc) = D.plus (cod_sface f) in
          let (Plus pw) = D.plus (dom_sface f) in
          let mc' = D.plus_assocr (Suc (Zero, g0)) plc mc in
          let (Wrap l) = Endpoints.wrapped () in
          M.apply
            (M.zip
               (fun () ->
                 BwvM.mapM
                   (fun e ->
                     gbuildM (Word m1) mc'
                       (sface_plus_sface (End (Zero, g0, e)) plc (D.zero_plus (dom_sface f)) f)
                       g)
                   (Endpoints.indices l))
               (fun () -> gbuildM (Word m1) mc' (sface_plus_sface (Mid (Zero, g0)) plc pw f) g))
          @@ fun (ends, mid) -> Branch (g0, pw, l, ends, mid)

    let buildM : type n b. n D.t -> (n, b) builderM -> (n, b) t M.t =
     fun n g -> gbuildM n Zero Zero g
  end

  module Monadic (M : Monad.Plain) = struct
    module A = Applicative.OfMonad (M)
    include Applicatic (A)
  end

  (* Now we can specialize all of them to the identity monad. *)

  module IdM = Monadic (Monad.Identity)

  let pmap : type n b bs cs.
      (n, (b, bs) cons, cs) IdM.pmapperM ->
      (n, D.zero, (b, bs) cons) Heter.hgt ->
      cs Tlist.t ->
      (n, D.zero, cs) Heter.hgt =
   fun g xs ys -> IdM.pmapM { map = (fun fa x -> g.map fa x) } xs ys

  let mmap : type n b bs c.
      (n, (b, bs) cons, c) IdM.mmapperM -> (n, D.zero, (b, bs) cons) Heter.hgt -> (n, c) t =
   fun g xs -> IdM.mmapM { map = (fun fa x -> g.map fa x) } xs

  let miter : type n b bs.
      (n, (b, bs) cons) IdM.miteratorM -> (n, D.zero, (b, bs) cons) Heter.hgt -> unit =
   fun g xs -> IdM.miterM { it = (fun fa x -> g.it fa x) } xs

  let build : type n b. n D.t -> (n, b) IdM.builderM -> (n, b) t =
   fun n g -> IdM.buildM n { build = (fun fa -> g.build fa) }

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

  (* In this special case, we can change the decided-word index fairly arbitrarily, although it takes a bit of work to convince OCaml.  (Of course, semantically these are identity functions.)  Lifting extends the decided word on the outside; the witnesses stored in the Branches are transported by associativity. *)

  let rec lift : type m w1 n2 w12 b. (w1, n2, w12) D.plus -> (m, w1, b) gt -> (m, w12, b) gt =
   fun w12 tr ->
    match tr with
    | Leaf x -> Leaf x
    | Branch (g, pw, l, ends, mid) ->
        let (Plus q) = D.plus (D.plus_right w12) in
        let pw' = D.plus_assocr pw w12 q in
        Branch (g, pw', l, Bwv.map (fun t -> lift w12 t) ends, lift q mid)

  let rec lower : type m w1 n2 w12 b. (m, w12, b) gt -> (w1, n2, w12) D.plus -> (m, w1, b) gt =
   fun tr w12 ->
    match tr with
    | Leaf x -> Leaf x
    | Branch (g, pw, l, ends, mid) ->
        let w1 = D.plus_left w12 (D.plus_right pw) in
        let (Plus pw') = D.plus w1 in
        let q = D.plus_assocl pw' w12 pw in
        Branch (g, pw', l, Bwv.map (fun t -> lower t w12) ends, lower mid q)
end
