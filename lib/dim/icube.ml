open Util
open Signatures
open Tlist
open Sface
module Fw = Fwsface

(* This is a version of the cube data structure whose indices can "count" some type-level data that is accumulated by what is stored.  For instance, if each entry is parametrized by a type-level natural number, then the cube data structure is parametrized by the total of all these numbers.  In fact it is parametrized by the operation of addition of this number, or more precisely by both an input and result for this operation. *)

module type Suc = sig
  type 'a suc
end

(* An Icube is parametrized by a "successor" type operation and a 3-variable family for the contents that are also parametrized by the "current count".  *)
module Icube (S : Suc) (F : Fam3) = struct
  (* The basic definitions are mostly just like those of Cube, with extra parameters.  As in Cube, the second dimension index 'w is the *forwards* word of generators decided (taken as Mid) along the path leading to a subtree; a Mid conses onto its head, and a Leaf reconciles it with the backwards dimension 'r via a bplus. *)
  type (_, _, _, _, _) gt =
    | Leaf :
        (D.zero, 'w, 'r) D.bplus * ('left, 'r, 'b) F.t
        -> ('left, D.zero, 'w, 'b, 'left S.suc) gt
    | Branch :
        'g D.G.t
        * 'l Endpoints.len
        * ('left, 'l, 'm, 'w, 'b, 'middle) branches
        * ('middle, 'm, ('g, 'w) cons, 'b, 'right) gt
        -> ('left, ('m, 'g) D.suc, 'w, 'b, 'right) gt

  (* The exception is that instead of using a vanilla Bwv, to index the branches we use a custom kind of backwards list that tracks the change in the indices. *)
  and (_, _, _, _, _, _) branches =
    | Emp : ('left, N.zero, 'm, 'w, 'b, 'left) branches
    | Snoc :
        ('left, 'l, 'm, 'w, 'b, 'middle) branches * ('middle, 'm, 'w, 'b, 'right) gt
        -> ('left, 'l N.suc, 'm, 'w, 'b, 'right) branches

  type ('left, 'n, 'b, 'right) t = ('left, 'n, D.fwd_zero, 'b, 'right) gt

  let rec gdim : type m w b left right. (left, m, w, b, right) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (g, _, _, br) -> D.suc (gdim br) g

  let dim : type n b left right. (left, n, b, right) t -> n D.t = fun tr -> gdim tr

  (* While we can't have a truly generic traversal, we can define some special cases.  The simplest one is "map" which applies some function to each entry, preserving all the indices on the nose. *)

  (* ********** Map ********** *)

  type ('n, 'b, 'c) mapper = {
    map : 'left 'right 'm. ('m, 'n) sface -> ('left, 'm, 'b) F.t -> ('left, 'm, 'c) F.t;
  }

  (* The traversal accumulates a forwards face, as in Cube: 'wf is the decided word (the fwsface domain) and 'cf the consumed word, related to the remaining height 'm and total dimension 'n by the bplus 'mc. *)
  let rec gmap : type m wf cf n b cc left right.
      (m, cf, n) D.bplus ->
      (wf, cf) Fw.fwsface ->
      (n, b, cc) mapper ->
      (left, m, wf, b, right) gt ->
      (left, m, wf, cc, right) gt =
   fun mc d g tr ->
    match tr with
    | Leaf (bp, x) ->
        let x = g.map (Fw.sface_of_fw bp mc d) x in
        Leaf (bp, x)
    | Branch (g0, l, ends, mid) ->
        let newends = gmap_branches (Append_cons mc) d g0 g (Endpoints.indices l) ends in
        let newmid = gmap (Append_cons mc) (Fw.Mid (g0, d)) g mid in
        Branch (g0, l, newends, newmid)

  and gmap_branches : type m1 wf cf n b cc len len' left right g0.
      (m1, (g0, cf) cons, n) D.bplus ->
      (wf, cf) Fw.fwsface ->
      g0 D.G.t ->
      (n, b, cc) mapper ->
      (len Endpoints.t, len') Bwv.t ->
      (left, len', m1, wf, b, right) branches ->
      (left, len', m1, wf, cc, right) branches =
   fun mc d g0 g ixs brs ->
    match (brs, ixs) with
    | Emp, Emp -> Emp
    | Snoc (brs, br), Snoc (ixs, e) ->
        let newbrs = gmap_branches mc d g0 g ixs brs in
        let newbr = gmap mc (Fw.End (g0, e, d)) g br in
        Snoc (newbrs, newbr)

  let map : type n b c left right.
      (n, b, c) mapper -> (left, n, b, right) t -> (left, n, c, right) t =
   fun g x -> gmap Append_nil Fw.Zero g x

  (* ********** Traversals with indexed state ********** *)

  (* The natural way to traverse or build an indexed cube is to maintain an accumulator that's indexed by the intermediate types.  Thus, for instance, from a plain cube regarded as one of these cubes, we can append all of its entries to some Bwv. *)

  module Traverse (Acc : Fam) = struct
    type ('n, 'b, 'c) left_folder = {
      foldmap :
        'left 'm.
        ('m, 'n) sface ->
        'left Acc.t ->
        ('left, 'm, 'b) F.t ->
        ('left, 'm, 'c) F.t * 'left S.suc Acc.t;
    }

    let rec gfold_map_left : type m wf cf n b cc left right.
        (m, cf, n) D.bplus ->
        (wf, cf) Fw.fwsface ->
        (n, b, cc) left_folder ->
        left Acc.t ->
        (left, m, wf, b, right) gt ->
        (left, m, wf, cc, right) gt * right Acc.t =
     fun mc d g acc tr ->
      match tr with
      | Leaf (bp, x) ->
          let x, acc = g.foldmap (Fw.sface_of_fw bp mc d) acc x in
          (Leaf (bp, x), acc)
      | Branch (g0, l, ends, mid) ->
          let ends, acc =
            gfold_left_map_branches (Append_cons mc) d g0 g (Endpoints.indices l) acc ends in
          let mid, acc = gfold_map_left (Append_cons mc) (Fw.Mid (g0, d)) g acc mid in
          (Branch (g0, l, ends, mid), acc)

    and gfold_left_map_branches : type m1 wf cf n b cc len len' left right g0.
        (m1, (g0, cf) cons, n) D.bplus ->
        (wf, cf) Fw.fwsface ->
        g0 D.G.t ->
        (n, b, cc) left_folder ->
        (len Endpoints.t, len') Bwv.t ->
        left Acc.t ->
        (left, len', m1, wf, b, right) branches ->
        (left, len', m1, wf, cc, right) branches * right Acc.t =
     fun mc d g0 g ixs acc brs ->
      match (brs, ixs) with
      | Emp, Emp -> (Emp, acc)
      | Snoc (brs, br), Snoc (ixs, e) ->
          let brs, acc = gfold_left_map_branches mc d g0 g ixs acc brs in
          let br, acc = gfold_map_left mc (Fw.End (g0, e, d)) g acc br in
          (Snoc (brs, br), acc)

    let fold_map_left : type n b c left right.
        (n, b, c) left_folder ->
        left Acc.t ->
        (left, n, b, right) t ->
        (left, n, c, right) t * right Acc.t =
     fun g acc x -> gfold_map_left Append_nil Fw.Zero g acc x

    (* And dually on the right. *)

    type ('n, 'b, 'c) right_folder = {
      foldmap :
        'left 'm.
        ('m, 'n) sface ->
        ('left, 'm, 'b) F.t ->
        'left S.suc Acc.t ->
        'left Acc.t * ('left, 'm, 'c) F.t;
    }

    let rec gfold_map_right : type m wf cf n b cc left right.
        (m, cf, n) D.bplus ->
        (wf, cf) Fw.fwsface ->
        (n, b, cc) right_folder ->
        (left, m, wf, b, right) gt ->
        right Acc.t ->
        left Acc.t * (left, m, wf, cc, right) gt =
     fun mc d g tr acc ->
      match tr with
      | Leaf (bp, x) ->
          let acc, x = g.foldmap (Fw.sface_of_fw bp mc d) x acc in
          (acc, Leaf (bp, x))
      | Branch (g0, l, ends, mid) ->
          let acc, mid = gfold_map_right (Append_cons mc) (Fw.Mid (g0, d)) g mid acc in
          let acc, ends =
            gfold_right_map_branches (Append_cons mc) d g0 g (Endpoints.indices l) ends acc in
          (acc, Branch (g0, l, ends, mid))

    and gfold_right_map_branches : type m1 wf cf n b cc len len' left right g0.
        (m1, (g0, cf) cons, n) D.bplus ->
        (wf, cf) Fw.fwsface ->
        g0 D.G.t ->
        (n, b, cc) right_folder ->
        (len Endpoints.t, len') Bwv.t ->
        (left, len', m1, wf, b, right) branches ->
        right Acc.t ->
        left Acc.t * (left, len', m1, wf, cc, right) branches =
     fun mc d g0 g ixs brs acc ->
      match (brs, ixs) with
      | Emp, Emp -> (acc, Emp)
      | Snoc (brs, br), Snoc (ixs, e) ->
          let acc, br = gfold_map_right mc (Fw.End (g0, e, d)) g br acc in
          let acc, brs = gfold_right_map_branches mc d g0 g ixs brs acc in
          (acc, Snoc (brs, br))

    let fold_map_right : type n b c left right.
        (n, b, c) right_folder ->
        (left, n, b, right) t ->
        right Acc.t ->
        left Acc.t * (left, n, c, right) t =
     fun g x acc -> gfold_map_right Append_nil Fw.Zero g x acc

    (* Similarly for building. *)

    type (_, _, _) fwrap_left =
      | Fwrap : ('left, 'm, 'b) F.t * 'left S.suc Acc.t -> ('left, 'm, 'b) fwrap_left

    type (_, _, _, _) gwrap_left =
      | Wrap : ('left, 'm, 'w, 'b, 'right) gt * 'right Acc.t -> ('left, 'm, 'w, 'b) gwrap_left

    type ('left, 'm, 'b) wrap_left = ('left, 'm, D.fwd_zero, 'b) gwrap_left

    type (_, _, _, _, _) wrap_branches_left =
      | Wrap_branches :
          ('left, 'len, 'm, 'w, 'b, 'right) branches * 'right Acc.t
          -> ('left, 'len, 'm, 'w, 'b) wrap_branches_left

    type ('n, 'b) builder_leftM = {
      build : 'left 'm. ('m, 'n) sface -> 'left Acc.t -> ('left, 'm, 'b) fwrap_left;
    }

    let rec gbuild_left : type m wf cf n b left.
        m D.t ->
        (m, cf, n) D.bplus ->
        (wf, cf) Fw.fwsface ->
        (n, b) builder_leftM ->
        left Acc.t ->
        (left, m, wf, b) gwrap_left =
     fun m mc d g acc ->
      match m with
      | Word Zero ->
          let (Bplus dbp) = D.bplus (Fw.dom_fwsface d) in
          let (Fwrap (x, acc)) = g.build (Fw.sface_of_fw dbp mc d) acc in
          Wrap (Leaf (dbp, x), acc)
      | Word (Suc (m1, g0)) ->
          let (Wrap l) = Endpoints.wrapped () in
          let (Wrap_branches (ends, acc)) =
            gbuild_left_branches (Word m1) (Append_cons mc) d g0 g (Endpoints.indices l) acc in
          let (Wrap (mid, acc)) =
            gbuild_left (Word m1) (Append_cons mc) (Fw.Mid (g0, d)) g acc in
          Wrap (Branch (g0, l, ends, mid), acc)

    and gbuild_left_branches : type m1 wf cf n b left len len' g0.
        m1 D.t ->
        (m1, (g0, cf) cons, n) D.bplus ->
        (wf, cf) Fw.fwsface ->
        g0 D.G.t ->
        (n, b) builder_leftM ->
        (len Endpoints.t, len') Bwv.t ->
        left Acc.t ->
        (left, len', m1, wf, b) wrap_branches_left =
     fun m mc d g0 g ixs acc ->
      match ixs with
      | Emp -> Wrap_branches (Emp, acc)
      | Snoc (ixs, e) ->
          let (Wrap_branches (newbrs, acc)) = gbuild_left_branches m mc d g0 g ixs acc in
          let (Wrap (newbr, acc)) = gbuild_left m mc (Fw.End (g0, e, d)) g acc in
          Wrap_branches (Snoc (newbrs, newbr), acc)

    let build_left : type n b left.
        n D.t -> (n, b) builder_leftM -> left Acc.t -> (left, n, b) wrap_left =
     fun n g acc -> gbuild_left n Append_nil Fw.Zero g acc
  end

  (* Indexing *)

  type (_, _) fbiwrap = Fbiwrap : ('left, 'n, 'b) F.t -> ('n, 'b) fbiwrap

  (* Walk the gt and the sface in lockstep, as in Cube.gfind; the carried bplus is transported by Append_cons at each Mid. *)
  let rec gfind : type m w b j p left right.
      (left, m, w, b, right) gt -> (j, m) sface -> (j, w, p) D.bplus -> (p, b) fbiwrap =
   fun tr d jw ->
    match (tr, d) with
    | Leaf (bp, x), Zero ->
        let Eq = D.bplus_uniq bp jw in
        Fbiwrap x
    | Branch (_, l1, br, _), End (d, _, (l2, e)) ->
        let Eq = Endpoints.uniq l1 l2 in
        gfind_branches br d jw e
    | Branch (_, _, _, br), Mid (d, _) -> gfind br d (Append_cons jw)

  and gfind_branches : type m w b j p left right l.
      (left, l, m, w, b, right) branches ->
      (j, m) sface ->
      (j, w, p) D.bplus ->
      l N.index ->
      (p, b) fbiwrap =
   fun br d jw e ->
    match (br, e) with
    | Emp, _ -> .
    | Snoc (_, tr), Top -> gfind tr d jw
    | Snoc (br, _), Pop e -> gfind_branches br d jw e

  let find : type n k b left right. (left, n, b, right) t -> (k, n) sface -> (k, b) fbiwrap =
   fun tr d -> gfind tr d Append_nil

  let rec gfind_top : type m w p b left right.
      (left, m, w, b, right) gt -> (m, w, p) D.bplus -> (p, b) fbiwrap =
   fun tr mw ->
    match tr with
    | Leaf (bp, x) ->
        let Eq = D.bplus_uniq bp mw in
        Fbiwrap x
    | Branch (_, _, _, br) -> gfind_top br (Append_cons mw)

  let find_top : type n b left right. (left, n, b, right) t -> (n, b) fbiwrap =
   fun tr -> gfind_top tr Append_nil
end

module IcubeTraverse2 (S1 : Suc) (S2 : Suc) (F1 : Fam3) (F2 : Fam3) (Acc : Fam2) = struct
  module C1 = Icube (S1) (F1)
  module C2 = Icube (S2) (F2)
  module Fw = Fwsface

  type ('n, 'b, 'c) left_folder = {
    foldmap :
      'left1 'left2 'm.
      ('m, 'n) sface ->
      ('left1, 'left2) Acc.t ->
      ('left1, 'm, 'b) F1.t ->
      ('left2, 'm, 'c) F2.t * ('left1 S1.suc, 'left2 S2.suc) Acc.t;
  }

  type (_, _, _, _, _) gfolded =
    | Gfolded :
        ('left2, 'm, 'w, 'c, 'right2) C2.gt * ('right1, 'right2) Acc.t
        -> ('left2, 'm, 'w, 'c, 'right1) gfolded

  type (_, _, _, _, _, _) gfolded_branches =
    | Gfolded_branches :
        ('left2, 'len, 'm, 'w, 'c, 'right2) C2.branches * ('right1, 'right2) Acc.t
        -> ('left2, 'len, 'm, 'w, 'c, 'right1) gfolded_branches

  let rec gfold_map_left : type m wf cf n b cc left1 left2 right1.
      (m, cf, n) D.bplus ->
      (wf, cf) Fw.fwsface ->
      (n, b, cc) left_folder ->
      (left1, left2) Acc.t ->
      (left1, m, wf, b, right1) C1.gt ->
      (left2, m, wf, cc, right1) gfolded =
   fun mc d g acc tr ->
    match tr with
    | Leaf (bp, x) ->
        let x, acc = g.foldmap (Fw.sface_of_fw bp mc d) acc x in
        Gfolded (Leaf (bp, x), acc)
    | Branch (g0, l, ends, mid) ->
        let (Gfolded_branches (ends, acc)) =
          gfold_left_map_branches (Append_cons mc) d g0 g (Endpoints.indices l) acc ends in
        let (Gfolded (mid, acc)) = gfold_map_left (Append_cons mc) (Fw.Mid (g0, d)) g acc mid in
        Gfolded (Branch (g0, l, ends, mid), acc)

  and gfold_left_map_branches : type m1 wf cf n b cc len len' left1 left2 right1 g0.
      (m1, (g0, cf) cons, n) D.bplus ->
      (wf, cf) Fw.fwsface ->
      g0 D.G.t ->
      (n, b, cc) left_folder ->
      (len Endpoints.t, len') Bwv.t ->
      (left1, left2) Acc.t ->
      (left1, len', m1, wf, b, right1) C1.branches ->
      (left2, len', m1, wf, cc, right1) gfolded_branches =
   fun mc d g0 g ixs acc brs ->
    match (brs, ixs) with
    | Emp, Emp -> Gfolded_branches (Emp, acc)
    | Snoc (brs, br), Snoc (ixs, e) ->
        let (Gfolded_branches (brs, acc)) = gfold_left_map_branches mc d g0 g ixs acc brs in
        let (Gfolded (br, acc)) = gfold_map_left mc (Fw.End (g0, e, d)) g acc br in
        Gfolded_branches (Snoc (brs, br), acc)

  let fold_map_left : type n b c left1 left2 right1.
      (n, b, c) left_folder ->
      (left1, left2) Acc.t ->
      (left1, n, D.fwd_zero, b, right1) C1.gt ->
      (left2, n, D.fwd_zero, c, right1) gfolded =
   fun g acc x -> gfold_map_left Append_nil Fw.Zero g acc x
end

(* The most important case of indexed cubes is when the indices are type-level natural numbers that simply count how many entries there are in the cube.  TODO: Would it be easier to implement this case directly rather than as a special case of the more general version above, and if so would it simplify other things?  E.g. require fewer type annotations in uses?  It might also allow generic traversals to work. *)

module NFamOf = struct
  type (_, _, _) t = NFamOf : 'b -> ('left, 'n, 'b) t
end

module NICubeOf = struct
  include Icube (N) (NFamOf)

  let singleton : type left b. b -> (left, D.zero, b, left N.suc) t =
   fun x -> Leaf (Append_nil, NFamOf x)

  module NFold = Traverse (N)

  let nfold : type left m n b.
      (m, n) sface -> left N.t -> (left, m, b) NFamOf.t -> (left, m, unit) NFamOf.t * left N.suc N.t
      =
   fun _ n (NFamOf _) -> (NFamOf (), N.suc n)

  let out : type left m b right. left N.t -> (left, m, b, right) t -> right N.t =
   fun l b -> snd (NFold.fold_map_left { foldmap = nfold } l b)

  let find : type n k b left right. (left, n, b, right) t -> (k, n) sface -> b =
   fun tr fa ->
    let (Fbiwrap (NFamOf x)) = find tr fa in
    x

  let find_top : type n b left right. (left, n, b, right) t -> b =
   fun tr ->
    let (Fbiwrap (NFamOf x)) = find_top tr in
    x
end
