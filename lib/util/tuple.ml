open Signatures
open Tlist
open Tbwd

(* A "tuple" is an intrinsically well-typed *total* map whose keys are insertions into some Word over a chosen generator type, and whose values are parametrized by the generator of the inserted element and the result of removing it.  *)

module Make (G : Comparable) (F : Fam3) = struct
  module W = Word.Make (G)

  type (_, _, _) gt =
    | Emp : (W.zero, 'b, 'p) gt
    | Map : {
        gen : 'g G.t;
        bplus : ('a, 'b, 'ab) W.bplus;
        now : ('g, 'ab, 'p) F.t;
        later : ('a, ('g, 'b) cons, 'p) gt;
      }
        -> (('a, 'g) snoc, 'b, 'p) gt

  type ('a, 'p) t = ('a, nil, 'p) gt

  let empty : type b p. (W.zero, b, p) gt = Emp

  let rec gfind : type a asuc g b ab p.
      (a, g, asuc) Tbwd.insert -> (asuc, b, p) gt -> (a, b, ab) W.bplus -> (g, ab, p) F.t =
   fun i m ab ->
    match i with
    | Now ->
        let (Map { bplus; now; _ }) = m in
        let Eq = W.bplus_uniq ab bplus in
        now
    | Later i ->
        let (Map { later; _ }) = m in
        gfind i later (Append_cons ab)

  let find : type a asuc g p. (a, g, asuc) Tbwd.insert -> (asuc, p) t -> (g, a, p) F.t =
   fun i m -> gfind i m Append_nil

  let rec gset : type a asuc g b ab p.
      (a, g, asuc) Tbwd.insert ->
      (g, ab, p) F.t ->
      (asuc, b, p) gt ->
      (a, b, ab) W.bplus ->
      (asuc, b, p) gt =
   fun i v m ab ->
    match i with
    | Now ->
        let (Map m) = m in
        let Eq = W.bplus_uniq ab m.bplus in
        Map { m with now = v }
    | Later i ->
        let (Map m) = m in
        Map { m with later = gset i v m.later (Append_cons ab) }

  let set : type a asuc g p. (a, g, asuc) Tbwd.insert -> (g, a, p) F.t -> (asuc, p) t -> (asuc, p) t
      =
   fun i v m -> gset i v m Append_nil

  let rec gupdate : type a asuc g b ab p.
      (a, g, asuc) Tbwd.insert ->
      ((g, ab, p) F.t -> (g, ab, p) F.t) ->
      (asuc, b, p) gt ->
      (a, b, ab) W.bplus ->
      (asuc, b, p) gt =
   fun i f m ab ->
    match i with
    | Now ->
        let (Map m) = m in
        let Eq = W.bplus_uniq ab m.bplus in
        Map { m with now = f m.now }
    | Later i ->
        let (Map m) = m in
        Map { m with later = gupdate i f m.later (Append_cons ab) }

  let update : type a asuc g p.
      (a, g, asuc) Tbwd.insert -> ((g, a, p) F.t -> (g, a, p) F.t) -> (asuc, p) t -> (asuc, p) t =
   fun i f m -> gupdate i f m Append_nil

  type ('asuc, 'p) builder = {
    build : 'a 'g. 'g G.t -> ('a, 'g, 'asuc) Tbwd.insert -> ('g, 'a, 'p) F.t;
  }

  let rec gbuild : type a b ab p. a W.t -> (a, b, ab) W.bplus -> (ab, p) builder -> (a, b, p) gt =
   fun a ab builder ->
    match a with
    | Word Zero -> Emp
    | Word (Suc (a', g)) ->
        let (Append bplus) = Tbwd.append (W.bplus_right ab) in
        Map
          {
            gen = g;
            bplus;
            now = builder.build g (W.insert_bplus Now bplus ab);
            later = gbuild (Word a') (Append_cons ab) builder;
          }

  let build : type a p. a W.t -> (a, p) builder -> (a, p) t =
   fun a builder -> gbuild a Append_nil builder

  (* Generic traversal *)

  module Heter = struct
    type (_, _, _) hft =
      | [] : ('g, 'a, nil) hft
      | ( :: ) : ('g, 'a, 'p) F.t * ('g, 'a, 'ps) hft -> ('g, 'a, ('p, 'ps) cons) hft

    type (_, _, _) hgt =
      | [] : ('a, 'b, nil) hgt
      | ( :: ) : ('a, 'b, 'p) gt * ('a, 'b, 'ps) hgt -> ('a, 'b, ('p, 'ps) cons) hgt

    let rec emp : type b ps. ps Tlist.t -> (W.zero, b, ps) hgt = function
      | Nil -> []
      | Cons ps -> Emp :: emp ps

    let rec map : type a b ab g ps.
        g G.t ->
        (a, b, ab) W.bplus ->
        (g, ab, ps) hft ->
        (a, (g, b) cons, ps) hgt ->
        ((a, g) snoc, b, ps) hgt =
     fun gen ab nows laters ->
      match (nows, laters) with
      | [], [] -> []
      | now :: nows, later :: laters ->
          Map { gen; bplus = ab; now; later } :: map gen ab nows laters

    let rec now : type a b ab g ps.
        (a, b, ab) W.bplus -> ((a, g) snoc, b, ps) hgt -> (g, ab, ps) hft =
     fun ab m ->
      match m with
      | [] -> []
      | Map { bplus; now = n; _ } :: ms ->
          let Eq = W.bplus_uniq ab bplus in
          n :: now ab ms

    let rec later : type a g b ps. ((a, g) snoc, b, ps) hgt -> (a, (g, b) cons, ps) hgt = function
      | [] -> []
      | Map { later = l; _ } :: ms -> l :: later ms
  end

  (* OCaml can't always tell from context what [x ; xs] should be; in particular it often fails to notice hfts.  So we also give a different syntax that is unambiguous.  *)
  module Infix = struct
    let hnil : type g n. (g, n, nil) Heter.hft = []

    let ( @: ) : type g n x xs.
        (g, n, x) F.t -> (g, n, xs) Heter.hft -> (g, n, (x, xs) cons) Heter.hft =
     fun x xs -> x :: xs
  end

  open Infix

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)

    type ('asuc, 'ps, 'qs) pmapperM = {
      map :
        'a 'g.
        'g G.t ->
        ('a, 'g, 'asuc) Tbwd.insert ->
        ('g, 'a, 'ps) Heter.hft ->
        ('g, 'a, 'qs) Heter.hft M.t;
    }

    let rec gpmapM : type a b ab p ps qs.
        (a, b, ab) W.bplus ->
        (ab, (p, ps) cons, qs) pmapperM ->
        (a, b, (p, ps) cons) Heter.hgt ->
        qs Tlist.t ->
        (a, b, qs) Heter.hgt M.t =
     fun ab f mss qs ->
      match mss with
      | Emp :: _ -> return (Heter.emp qs)
      | Map { gen; bplus = ab'; now = v; later } :: mss ->
          M.apply
            (M.zip
               (fun () -> f.map gen (W.insert_bplus Now ab' ab) (v :: Heter.now ab' mss))
               (fun () -> gpmapM (Append_cons ab) f (later :: Heter.later mss) qs))
          @@ fun (fnow, flater) -> Heter.map gen ab' fnow flater

    let pmapM : type a p ps qs.
        (a, (p, ps) cons, qs) pmapperM ->
        (a, nil, (p, ps) cons) Heter.hgt ->
        qs Tlist.t ->
        (a, nil, qs) Heter.hgt M.t =
     fun f mss qs -> gpmapM Append_nil f mss qs

    type ('asuc, 'ps, 'q) mmapperM = {
      map :
        'a 'g.
        'g G.t -> ('a, 'g, 'asuc) Tbwd.insert -> ('g, 'a, 'ps) Heter.hft -> ('g, 'a, 'q) F.t M.t;
    }

    let mmapM : type a p ps q.
        (a, (p, ps) cons, q) mmapperM -> (a, nil, (p, ps) cons) Heter.hgt -> (a, nil, q) gt M.t =
     fun f xs ->
      M.apply
        (pmapM { map = (fun g i x -> M.apply (f.map g i x) @@ fun y -> y @: hnil) } xs (Cons Nil))
      @@ fun [ ys ] -> ys

    type ('asuc, 'ps) miteratorM = {
      it : 'a 'g. 'g G.t -> ('a, 'g, 'asuc) Tbwd.insert -> ('g, 'a, 'ps) Heter.hft -> unit M.t;
    }

    let miterM : type a p ps.
        (a, (p, ps) cons) miteratorM -> (a, nil, (p, ps) cons) Heter.hgt -> unit M.t =
     fun f xs ->
      M.apply (pmapM { map = (fun g i x -> M.apply (f.it g i x) @@ fun () -> hnil) } xs Nil)
      @@ fun [] -> ()
  end

  module Monadic (M : Monad.Plain) = struct
    module A = Applicative.OfMonad (M)
    include Applicatic (A)
  end

  module IdM = Monadic (Monad.Identity)

  let pmap f xs qs = IdM.pmapM f xs qs
  let mmap f xs = IdM.mmapM f xs
  let miter f xs = IdM.miterM f xs
end
