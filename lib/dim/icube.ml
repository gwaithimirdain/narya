open Util
open Signatures
open Sface

(* This is a version of the cube data structure whose indices can "count" some type-level data that is accumulated by what is stored.  For instance, if each entry is parametrized by a type-level natural number, then the cube data structure is parametrized by the total of all these numbers.  In fact it is parametrized by the operation of addition of this number, or more precisely by both an input and result for this operation. *)

module type Suc = sig
  type 'a suc
end

(* An Icube is parametrized by a "successor" type operation and a 3-variable family for the contents that are also parametrized by the "current count".  *)
module Icube (S : Suc) (F : Fam3) = struct
  (* The basic definitions are mostly just like those of Cube, with extra parameters.  As in Cube, the second dimension index 'w is the word of generators decided (taken as Mid) along the path leading to a subtree, with the witness for adding a newly decided generator at its inner end stored in the Branch. *)
  type (_, _, _, _, _) gt =
    | Leaf : ('left, 'w, 'b) F.t -> ('left, D.zero, 'w, 'b, 'left S.suc) gt
    | Branch :
        'g D.G.t
        * ((D.zero, 'g) D.suc, 'w, 'gw) D.plus
        * 'l Endpoints.len
        * ('left, 'l, 'm, 'w, 'b, 'middle) branches
        * ('middle, 'm, 'gw, 'b, 'right) gt
        -> ('left, ('m, 'g) D.suc, 'w, 'b, 'right) gt

  (* The exception is that instead of using a vanilla Bwv, to index the branches we use a custom kind of backwards list that tracks the change in the indices. *)
  and (_, _, _, _, _, _) branches =
    | Emp : ('left, N.zero, 'm, 'w, 'b, 'left) branches
    | Snoc :
        ('left, 'l, 'm, 'w, 'b, 'middle) branches * ('middle, 'm, 'w, 'b, 'right) gt
        -> ('left, 'l N.suc, 'm, 'w, 'b, 'right) branches

  type ('left, 'n, 'b, 'right) t = ('left, 'n, D.zero, 'b, 'right) gt

  let rec gdim : type m w b left right. (left, m, w, b, right) gt -> m D.t = function
    | Leaf _ -> D.zero
    | Branch (g, _, _, _, br) -> D.suc (gdim br) g

  let dim : type n b left right. (left, n, b, right) t -> n D.t = fun tr -> gdim tr

  (* While we can't have a truly generic traversal, we can define some special cases.  The simplest one is "map" which applies some function to each entry, preserving all the indices on the nose.  Like the traversal of Cube, but unlike the others below, it makes sense in any applicative functor. *)

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)

    (* ********** Map ********** *)

    type ('n, 'b, 'c) mapperM = {
      map : 'left 'right 'm. ('m, 'n) sface -> ('left, 'm, 'b) F.t -> ('left, 'm, 'c) F.t M.t;
    }

    (* The traversal carries the partial strict face accumulated so far, as in Cube: 'w is the decided word and 'c the consumed word, related to the remaining height 'm and the total dimension 'n by the (m, c, n) plus. *)
    let rec gmapM : type m w c n b cc left right.
        (m, c, n) D.plus ->
        (w, c) sface ->
        (n, b, cc) mapperM ->
        (left, m, w, b, right) gt ->
        (left, m, w, cc, right) gt M.t =
     fun mc f g tr ->
      match tr with
      | Leaf x ->
          let Eq = D.zero_plus_uniq mc in
          M.apply (g.map f x) @@ fun x -> Leaf x
      | Branch (g0, pw, l, ends, mid) ->
          let (Plus plc) = D.plus (cod_sface f) in
          let mc' = D.plus_assocr (Suc (Zero, g0)) plc mc in
          M.apply
            (M.zip
               (fun () -> gmapM_branches mc' f plc g0 g (Endpoints.indices l) ends)
               (fun () -> gmapM mc' (sface_plus_sface (Mid (Zero, g0)) plc pw f) g mid))
          @@ fun (newends, newmid) -> Branch (g0, pw, l, newends, newmid)

    and gmapM_branches : type m1 w c gc n b cc len len' left right g0.
        (m1, gc, n) D.plus ->
        (w, c) sface ->
        ((D.zero, g0) D.suc, c, gc) D.plus ->
        g0 D.G.t ->
        (n, b, cc) mapperM ->
        (len Endpoints.t, len') Bwv.t ->
        (left, len', m1, w, b, right) branches ->
        (left, len', m1, w, cc, right) branches M.t =
     fun mc f plc g0 g ixs brs ->
      match (brs, ixs) with
      | Emp, Emp -> return Emp
      | Snoc (brs, br), Snoc (ixs, e) ->
          M.apply
            (M.zip
               (fun () -> gmapM_branches mc f plc g0 g ixs brs)
               (fun () ->
                 gmapM mc
                   (sface_plus_sface (End (Zero, g0, e)) plc (D.zero_plus (dom_sface f)) f)
                   g br))
          @@ fun (newbrs, newbr) -> Snoc (newbrs, newbr)

    let mapM : type n b c left right.
        (n, b, c) mapperM -> (left, n, b, right) t -> (left, n, c, right) t M.t =
     fun g x -> gmapM Zero Zero g x
  end

  module IdM = Applicatic (Applicative.OfMonad (Monad.Identity))

  let map : type n b c left right.
      (n, b, c) IdM.mapperM -> (left, n, b, right) t -> (left, n, c, right) t =
   fun g x -> IdM.mapM g x

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

    let rec gfold_map_left : type m w c n b cc left right.
        (m, c, n) D.plus ->
        (w, c) sface ->
        (n, b, cc) left_folder ->
        left Acc.t ->
        (left, m, w, b, right) gt ->
        (left, m, w, cc, right) gt * right Acc.t =
     fun mc f g acc tr ->
      match tr with
      | Leaf x ->
          let Eq = D.zero_plus_uniq mc in
          let x, acc = g.foldmap f acc x in
          (Leaf x, acc)
      | Branch (g0, pw, l, ends, mid) ->
          let (Plus plc) = D.plus (cod_sface f) in
          let mc' = D.plus_assocr (Suc (Zero, g0)) plc mc in
          let ends, acc = gfold_left_map_branches mc' f plc g0 g (Endpoints.indices l) acc ends in
          let mid, acc = gfold_map_left mc' (sface_plus_sface (Mid (Zero, g0)) plc pw f) g acc mid in
          (Branch (g0, pw, l, ends, mid), acc)

    and gfold_left_map_branches : type m1 w c gc n b cc len len' left right g0.
        (m1, gc, n) D.plus ->
        (w, c) sface ->
        ((D.zero, g0) D.suc, c, gc) D.plus ->
        g0 D.G.t ->
        (n, b, cc) left_folder ->
        (len Endpoints.t, len') Bwv.t ->
        left Acc.t ->
        (left, len', m1, w, b, right) branches ->
        (left, len', m1, w, cc, right) branches * right Acc.t =
     fun mc f plc g0 g ixs acc brs ->
      match (brs, ixs) with
      | Emp, Emp -> (Emp, acc)
      | Snoc (brs, br), Snoc (ixs, e) ->
          let brs, acc = gfold_left_map_branches mc f plc g0 g ixs acc brs in
          let br, acc =
            gfold_map_left mc
              (sface_plus_sface (End (Zero, g0, e)) plc (D.zero_plus (dom_sface f)) f)
              g acc br in
          (Snoc (brs, br), acc)

    let fold_map_left : type n b c left right.
        (n, b, c) left_folder ->
        left Acc.t ->
        (left, n, b, right) t ->
        (left, n, c, right) t * right Acc.t =
     fun g acc x -> gfold_map_left Zero Zero g acc x

    (* And dually on the right. *)

    type ('n, 'b, 'c) right_folder = {
      foldmap :
        'left 'm.
        ('m, 'n) sface ->
        ('left, 'm, 'b) F.t ->
        'left S.suc Acc.t ->
        'left Acc.t * ('left, 'm, 'c) F.t;
    }

    let rec gfold_map_right : type m w c n b cc left right.
        (m, c, n) D.plus ->
        (w, c) sface ->
        (n, b, cc) right_folder ->
        (left, m, w, b, right) gt ->
        right Acc.t ->
        left Acc.t * (left, m, w, cc, right) gt =
     fun mc f g tr acc ->
      match tr with
      | Leaf x ->
          let Eq = D.zero_plus_uniq mc in
          let acc, x = g.foldmap f x acc in
          (acc, Leaf x)
      | Branch (g0, pw, l, ends, mid) ->
          let (Plus plc) = D.plus (cod_sface f) in
          let mc' = D.plus_assocr (Suc (Zero, g0)) plc mc in
          let acc, mid =
            gfold_map_right mc' (sface_plus_sface (Mid (Zero, g0)) plc pw f) g mid acc in
          let acc, ends = gfold_right_map_branches mc' f plc g0 g (Endpoints.indices l) ends acc in
          (acc, Branch (g0, pw, l, ends, mid))

    and gfold_right_map_branches : type m1 w c gc n b cc len len' left right g0.
        (m1, gc, n) D.plus ->
        (w, c) sface ->
        ((D.zero, g0) D.suc, c, gc) D.plus ->
        g0 D.G.t ->
        (n, b, cc) right_folder ->
        (len Endpoints.t, len') Bwv.t ->
        (left, len', m1, w, b, right) branches ->
        right Acc.t ->
        left Acc.t * (left, len', m1, w, cc, right) branches =
     fun mc f plc g0 g ixs brs acc ->
      match (brs, ixs) with
      | Emp, Emp -> (acc, Emp)
      | Snoc (brs, br), Snoc (ixs, e) ->
          let acc, br =
            gfold_map_right mc
              (sface_plus_sface (End (Zero, g0, e)) plc (D.zero_plus (dom_sface f)) f)
              g br acc in
          let acc, brs = gfold_right_map_branches mc f plc g0 g ixs brs acc in
          (acc, Snoc (brs, br))

    let fold_map_right : type n b c left right.
        (n, b, c) right_folder ->
        (left, n, b, right) t ->
        right Acc.t ->
        left Acc.t * (left, n, c, right) t =
     fun g x acc -> gfold_map_right Zero Zero g x acc

    (* Similarly for building. *)

    type (_, _, _) fwrap_left =
      | Fwrap : ('left, 'm, 'b) F.t * 'left S.suc Acc.t -> ('left, 'm, 'b) fwrap_left

    type (_, _, _, _) gwrap_left =
      | Wrap : ('left, 'm, 'w, 'b, 'right) gt * 'right Acc.t -> ('left, 'm, 'w, 'b) gwrap_left

    type ('left, 'm, 'b) wrap_left = ('left, 'm, D.zero, 'b) gwrap_left

    type (_, _, _, _, _) wrap_branches_left =
      | Wrap_branches :
          ('left, 'len, 'm, 'w, 'b, 'right) branches * 'right Acc.t
          -> ('left, 'len, 'm, 'w, 'b) wrap_branches_left

    type ('n, 'b) builder_leftM = {
      build : 'left 'm. ('m, 'n) sface -> 'left Acc.t -> ('left, 'm, 'b) fwrap_left;
    }

    let rec gbuild_left : type m w c n b left.
        m D.t ->
        (m, c, n) D.plus ->
        (w, c) sface ->
        (n, b) builder_leftM ->
        left Acc.t ->
        (left, m, w, b) gwrap_left =
     fun m mc f g acc ->
      match m with
      | Word Zero ->
          let Eq = D.zero_plus_uniq mc in
          let (Fwrap (x, acc)) = g.build f acc in
          Wrap (Leaf x, acc)
      | Word (Suc (m1, g0)) ->
          let (Plus plc) = D.plus (cod_sface f) in
          let (Plus pw) = D.plus (dom_sface f) in
          let mc' = D.plus_assocr (Suc (Zero, g0)) plc mc in
          let (Wrap l) = Endpoints.wrapped () in
          let (Wrap_branches (ends, acc)) =
            gbuild_left_branches (Word m1) mc' f plc g0 g (Endpoints.indices l) acc in
          let (Wrap (mid, acc)) =
            gbuild_left (Word m1) mc' (sface_plus_sface (Mid (Zero, g0)) plc pw f) g acc in
          Wrap (Branch (g0, pw, l, ends, mid), acc)

    and gbuild_left_branches : type m1 w c gc n b left len len' g0.
        m1 D.t ->
        (m1, gc, n) D.plus ->
        (w, c) sface ->
        ((D.zero, g0) D.suc, c, gc) D.plus ->
        g0 D.G.t ->
        (n, b) builder_leftM ->
        (len Endpoints.t, len') Bwv.t ->
        left Acc.t ->
        (left, len', m1, w, b) wrap_branches_left =
     fun m mc f plc g0 g ixs acc ->
      match ixs with
      | Emp -> Wrap_branches (Emp, acc)
      | Snoc (ixs, e) ->
          let (Wrap_branches (newbrs, acc)) = gbuild_left_branches m mc f plc g0 g ixs acc in
          let (Wrap (newbr, acc)) =
            gbuild_left m mc
              (sface_plus_sface (End (Zero, g0, e)) plc (D.zero_plus (dom_sface f)) f)
              g acc in
          Wrap_branches (Snoc (newbrs, newbr), acc)

    let build_left : type n b left.
        n D.t -> (n, b) builder_leftM -> left Acc.t -> (left, n, b) wrap_left =
     fun n g acc -> gbuild_left n Zero Zero g acc
  end

  (* Indexing *)

  type (_, _) fbiwrap = Fbiwrap : ('left, 'n, 'b) F.t -> ('n, 'b) fbiwrap

  (* Walk the gt and the sface in lockstep, as in Cube.gfind; the carried plus relation is transported by associativity using the witnesses stored in the Branches. *)
  let rec gfind : type m w b j p left right.
      (left, m, w, b, right) gt -> (j, m) sface -> (j, w, p) D.plus -> (p, b) fbiwrap =
   fun tr d jw ->
    match (tr, d) with
    | Leaf x, Zero ->
        let Eq = D.zero_plus_uniq jw in
        Fbiwrap x
    | Branch (_, _, l1, br, _), End (d, _, (l2, e)) ->
        let Eq = Endpoints.uniq l1 l2 in
        gfind_branches br d jw e
    | Branch (_, pw, _, _, br), Mid (d, g) -> gfind br d (D.plus_assocr (Suc (Zero, g)) pw jw)

  and gfind_branches : type m w b j p left right l.
      (left, l, m, w, b, right) branches ->
      (j, m) sface ->
      (j, w, p) D.plus ->
      l N.index ->
      (p, b) fbiwrap =
   fun br d jw e ->
    match (br, e) with
    | Emp, _ -> .
    | Snoc (_, tr), Top -> gfind tr d jw
    | Snoc (br, _), Pop e -> gfind_branches br d jw e

  let find : type n k b left right. (left, n, b, right) t -> (k, n) sface -> (k, b) fbiwrap =
   fun tr d -> gfind tr d Zero

  let rec gfind_top : type m w p b left right.
      (left, m, w, b, right) gt -> (m, w, p) D.plus -> (p, b) fbiwrap =
   fun tr mw ->
    match tr with
    | Leaf x ->
        let Eq = D.zero_plus_uniq mw in
        Fbiwrap x
    | Branch (g, pw, _, _, br) -> gfind_top br (D.plus_assocr (Suc (Zero, g)) pw mw)

  let find_top : type n b left right. (left, n, b, right) t -> (n, b) fbiwrap =
   fun tr -> gfind_top tr Zero
end

module IcubeTraverse2 (S1 : Suc) (S2 : Suc) (F1 : Fam3) (F2 : Fam3) (Acc : Fam2) = struct
  module C1 = Icube (S1) (F1)
  module C2 = Icube (S2) (F2)

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

  let rec gfold_map_left : type m w c n b cc left1 left2 right1.
      (m, c, n) D.plus ->
      (w, c) sface ->
      (n, b, cc) left_folder ->
      (left1, left2) Acc.t ->
      (left1, m, w, b, right1) C1.gt ->
      (left2, m, w, cc, right1) gfolded =
   fun mc f g acc tr ->
    match tr with
    | Leaf x ->
        let Eq = D.zero_plus_uniq mc in
        let x, acc = g.foldmap f acc x in
        Gfolded (Leaf x, acc)
    | Branch (g0, pw, l, ends, mid) ->
        let (Plus plc) = D.plus (cod_sface f) in
        let mc' = D.plus_assocr (Suc (Zero, g0)) plc mc in
        let (Gfolded_branches (ends, acc)) =
          gfold_left_map_branches mc' f plc g0 g (Endpoints.indices l) acc ends in
        let (Gfolded (mid, acc)) =
          gfold_map_left mc' (sface_plus_sface (Mid (Zero, g0)) plc pw f) g acc mid in
        Gfolded (Branch (g0, pw, l, ends, mid), acc)

  and gfold_left_map_branches : type m1 w c gc n b cc len len' left1 left2 right1 g0.
      (m1, gc, n) D.plus ->
      (w, c) sface ->
      ((D.zero, g0) D.suc, c, gc) D.plus ->
      g0 D.G.t ->
      (n, b, cc) left_folder ->
      (len Endpoints.t, len') Bwv.t ->
      (left1, left2) Acc.t ->
      (left1, len', m1, w, b, right1) C1.branches ->
      (left2, len', m1, w, cc, right1) gfolded_branches =
   fun mc f plc g0 g ixs acc brs ->
    match (brs, ixs) with
    | Emp, Emp -> Gfolded_branches (Emp, acc)
    | Snoc (brs, br), Snoc (ixs, e) ->
        let (Gfolded_branches (brs, acc)) = gfold_left_map_branches mc f plc g0 g ixs acc brs in
        let (Gfolded (br, acc)) =
          gfold_map_left mc
            (sface_plus_sface (End (Zero, g0, e)) plc (D.zero_plus (dom_sface f)) f)
            g acc br in
        Gfolded_branches (Snoc (brs, br), acc)

  let fold_map_left : type n b c left1 left2 right1.
      (n, b, c) left_folder ->
      (left1, left2) Acc.t ->
      (left1, n, D.zero, b, right1) C1.gt ->
      (left2, n, D.zero, c, right1) gfolded =
   fun g acc x -> gfold_map_left Zero Zero g acc x
end

(* The most important case of indexed cubes is when the indices are type-level natural numbers that simply count how many entries there are in the cube.  TODO: Would it be easier to implement this case directly rather than as a special case of the more general version above, and if so would it simplify other things?  E.g. require fewer type annotations in uses?  It might also allow generic traversals to work. *)

module NFamOf = struct
  type (_, _, _) t = NFamOf : 'b -> ('left, 'n, 'b) t
end

module NICubeOf = struct
  include Icube (N) (NFamOf)

  let singleton : type left b. b -> (left, D.zero, b, left N.suc) t = fun x -> Leaf (NFamOf x)

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
