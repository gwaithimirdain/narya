open Signatures
open Tlist
open Tbwd

(* A "tuple" is an intrinsically well-typed map whose keys are insertions into some Word over a chosen generator type.  It is parametrized by an explicit "target" generator 'g0, and stores a value only at those keys whose inserted generator equals 'g0; at keys with any other generator it stores only an apartness witness (no closures, hence marshallable).  Callers therefore need not deal with the mismatched case themselves. *)

module Make (G : Decidable) (F : Fam2) = struct
  module W = Word.Make (G)

  type (_, _, _, _) gt =
    | Emp : (W.zero, 'b, 'g0, 'p) gt
    (* A key whose generator matches the target 'g0: we store an actual value. *)
    | Match : {
        bplus : ('a, 'b, 'ab) W.bplus;
        now : ('ab, 'p) F.t;
        later : ('a, ('g0, 'b) cons, 'g0, 'p) gt;
      }
        -> (('a, 'g0) snoc, 'b, 'g0, 'p) gt
    (* A key whose generator is apart from the target: we store only the apartness witness. *)
    | Miss : {
        gen : 'g G.t;
        apart : ('g, 'g0) G.apart;
        bplus : ('a, 'b, 'ab) W.bplus;
        later : ('a, ('g, 'b) cons, 'g0, 'p) gt;
      }
        -> (('a, 'g) snoc, 'b, 'g0, 'p) gt

  type ('a, 'g0, 'p) t = ('a, nil, 'g0, 'p) gt

  let empty : type b g0 p. (W.zero, b, g0, p) gt = Emp

  let rec gfind : type a asuc g0 b ab p.
      (a, g0, asuc) Tbwd.insert -> (asuc, b, g0, p) gt -> (a, b, ab) W.bplus -> (ab, p) F.t =
   fun i m ab ->
    match (i, m) with
    | Now, Match { bplus; now; _ } ->
        let Eq = W.bplus_uniq ab bplus in
        now
    | Now, Miss { apart; _ } -> ( match G.apart_irrefl apart with _ -> . )
    | Later i, Match { later; _ } -> gfind i later (Append_cons ab)
    | Later i, Miss { later; _ } -> gfind i later (Append_cons ab)

  let find : type a asuc g0 p. (a, g0, asuc) Tbwd.insert -> (asuc, g0, p) t -> (a, p) F.t =
   fun i m -> gfind i m Append_nil

  let rec gset : type a asuc g0 b ab p.
      (a, g0, asuc) Tbwd.insert ->
      (ab, p) F.t ->
      (asuc, b, g0, p) gt ->
      (a, b, ab) W.bplus ->
      (asuc, b, g0, p) gt =
   fun i v m ab ->
    match (i, m) with
    | Now, Match m ->
        let Eq = W.bplus_uniq ab m.bplus in
        Match { m with now = v }
    | Now, Miss { apart; _ } -> ( match G.apart_irrefl apart with _ -> . )
    | Later i, Match m -> Match { m with later = gset i v m.later (Append_cons ab) }
    | Later i, Miss m -> Miss { m with later = gset i v m.later (Append_cons ab) }

  let set : type a asuc g0 p.
      (a, g0, asuc) Tbwd.insert -> (a, p) F.t -> (asuc, g0, p) t -> (asuc, g0, p) t =
   fun i v m -> gset i v m Append_nil

  let rec gupdate : type a asuc g0 b ab p.
      (a, g0, asuc) Tbwd.insert ->
      ((ab, p) F.t -> (ab, p) F.t) ->
      (asuc, b, g0, p) gt ->
      (a, b, ab) W.bplus ->
      (asuc, b, g0, p) gt =
   fun i f m ab ->
    match (i, m) with
    | Now, Match m ->
        let Eq = W.bplus_uniq ab m.bplus in
        Match { m with now = f m.now }
    | Now, Miss { apart; _ } -> ( match G.apart_irrefl apart with _ -> . )
    | Later i, Match m -> Match { m with later = gupdate i f m.later (Append_cons ab) }
    | Later i, Miss m -> Miss { m with later = gupdate i f m.later (Append_cons ab) }

  let update : type a asuc g0 p.
      (a, g0, asuc) Tbwd.insert -> ((a, p) F.t -> (a, p) F.t) -> (asuc, g0, p) t -> (asuc, g0, p) t =
   fun i f m -> gupdate i f m Append_nil

  type ('asuc, 'g0, 'p) builder = { build : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'p) F.t }

  let rec gbuild : type a b ab g0 p.
      a W.t -> g0 G.t -> (a, b, ab) W.bplus -> (ab, g0, p) builder -> (a, b, g0, p) gt =
   fun a g0 ab builder ->
    match a with
    | Word Zero -> Emp
    | Word (Suc (a', g)) -> (
        let (Append bplus) = Tbwd.append (W.bplus_right ab) in
        match G.decide g g0 with
        | Same ->
            Match
              {
                bplus;
                now = builder.build (W.insert_bplus Now bplus ab);
                later = gbuild (Word a') g0 (Append_cons ab) builder;
              }
        | Distinct apart ->
            Miss { gen = g; apart; bplus; later = gbuild (Word a') g0 (Append_cons ab) builder })

  let build : type a g0 p. a W.t -> g0 G.t -> (a, g0, p) builder -> (a, g0, p) t =
   fun a g0 builder -> gbuild a g0 Append_nil builder

  (* Generic traversal *)

  module Heter = struct
    type (_, _) hft =
      | [] : ('a, nil) hft
      | ( :: ) : ('a, 'p) F.t * ('a, 'ps) hft -> ('a, ('p, 'ps) cons) hft

    type (_, _, _, _) hgt =
      | [] : ('a, 'b, 'g0, nil) hgt
      | ( :: ) :
          ('a, 'b, 'g0, 'p) gt * ('a, 'b, 'g0, 'ps) hgt
          -> ('a, 'b, 'g0, ('p, 'ps) cons) hgt

    let rec emp : type b g0 ps. ps Tlist.t -> (W.zero, b, g0, ps) hgt = function
      | Nil -> []
      | Cons ps -> Emp :: emp ps

    (* Extract the values from a heterogeneous list of Match nodes. *)
    let rec nows : type a b ab g0 ps.
        (a, b, ab) W.bplus -> ((a, g0) snoc, b, g0, ps) hgt -> (ab, ps) hft =
     fun ab m ->
      match m with
      | [] -> []
      | Match { bplus; now = n; _ } :: ms ->
          let Eq = W.bplus_uniq ab bplus in
          n :: nows ab ms
      | Miss { apart; _ } :: _ -> ( match G.apart_irrefl apart with _ -> . )

    (* Extract the sub-tuples of a heterogeneous list of Match (resp. Miss) nodes. *)
    let rec later_match : type a b g0 ps.
        ((a, g0) snoc, b, g0, ps) hgt -> (a, (g0, b) cons, g0, ps) hgt = function
      | [] -> []
      | Match { later = l; _ } :: ms -> l :: later_match ms
      | Miss { apart; _ } :: _ -> ( match G.apart_irrefl apart with _ -> . )

    let rec later_miss : type a b g g0 ps.
        (g, g0) G.apart -> ((a, g) snoc, b, g0, ps) hgt -> (a, (g, b) cons, g0, ps) hgt =
     fun apart -> function
      | [] -> []
      | Miss { later = l; _ } :: ms -> l :: later_miss apart ms
      | Match _ :: _ -> ( match G.apart_irrefl apart with _ -> . )

    (* Reassemble a heterogeneous list of Match (resp. Miss) nodes. *)
    let rec map_match : type a b ab g0 ps.
        (a, b, ab) W.bplus ->
        (ab, ps) hft ->
        (a, (g0, b) cons, g0, ps) hgt ->
        ((a, g0) snoc, b, g0, ps) hgt =
     fun ab nows laters ->
      match (nows, laters) with
      | [], [] -> []
      | now :: nows, later :: laters -> Match { bplus = ab; now; later } :: map_match ab nows laters

    let rec map_miss : type a b ab g g0 ps.
        g G.t ->
        (g, g0) G.apart ->
        (a, b, ab) W.bplus ->
        (a, (g, b) cons, g0, ps) hgt ->
        ((a, g) snoc, b, g0, ps) hgt =
     fun gen apart ab laters ->
      match laters with
      | [] -> []
      | later :: laters -> Miss { gen; apart; bplus = ab; later } :: map_miss gen apart ab laters
  end

  (* OCaml can't always tell from context what [x ; xs] should be; in particular it often fails to notice hfts.  So we also give a different syntax that is unambiguous.  *)
  module Infix = struct
    let hnil : type n. (n, nil) Heter.hft = []

    let ( @: ) : type n x xs. (n, x) F.t -> (n, xs) Heter.hft -> (n, (x, xs) cons) Heter.hft =
     fun x xs -> x :: xs
  end

  open Infix

  type ('asuc, 'g0, 'ps, 'qs) pmapper = {
    map : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'qs) Heter.hft;
  }

  let rec gpmap : type a b ab g0 p ps qs.
      (a, b, ab) W.bplus ->
      (ab, g0, (p, ps) cons, qs) pmapper ->
      (a, b, g0, (p, ps) cons) Heter.hgt ->
      qs Tlist.t ->
      (a, b, g0, qs) Heter.hgt =
   fun ab f mss qs ->
    match mss with
    | Emp :: _ -> Heter.emp qs
    | Match { bplus = ab'; now = v; later } :: mss ->
        let fnow = f.map (W.insert_bplus Now ab' ab) (v :: Heter.nows ab' mss) in
        let flater = gpmap (Append_cons ab) f (later :: Heter.later_match mss) qs in
        Heter.map_match ab' fnow flater
    | Miss { gen; apart; bplus = ab'; later } :: mss ->
        let flater = gpmap (Append_cons ab) f (later :: Heter.later_miss apart mss) qs in
        Heter.map_miss gen apart ab' flater

  let pmap : type a g0 p ps qs.
      (a, g0, (p, ps) cons, qs) pmapper ->
      (a, nil, g0, (p, ps) cons) Heter.hgt ->
      qs Tlist.t ->
      (a, nil, g0, qs) Heter.hgt =
   fun f mss qs -> gpmap Append_nil f mss qs

  type ('asuc, 'g0, 'ps, 'q) mmapper = {
    map : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'q) F.t;
  }

  let mmap : type a g0 p ps q.
      (a, g0, (p, ps) cons, q) mmapper ->
      (a, nil, g0, (p, ps) cons) Heter.hgt ->
      (a, nil, g0, q) gt =
   fun f xs ->
    let [ ys ] =
      pmap
        {
          map =
            (fun i x ->
              let y = f.map i x in
              y @: hnil);
        }
        xs (Cons Nil) in
    ys

  type ('asuc, 'g0, 'ps) miterator = {
    it : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> unit;
  }

  let miter : type a g0 p ps.
      (a, g0, (p, ps) cons) miterator -> (a, nil, g0, (p, ps) cons) Heter.hgt -> unit =
   fun f xs ->
    let [] =
      pmap
        {
          map =
            (fun i x ->
              f.it i x;
              hnil);
        }
        xs Nil in
    ()
end
