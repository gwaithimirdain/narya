open Dim
open Pairing

(* A "geometrically well-pointed topos" (gwpt) has two modes, Disc and Type, and four generating modalities:

     △ : Disc → Type     □ : Type → Disc
     ∇ : Disc → Type     ◇ : Type → Disc

   with two adjunctions △ ⊣ □ and ◇ ⊣ ∇, where:

   - the unit η : 1_Disc ⇒ □△ and counit ε : △□ ⇒ 1_Type of △ ⊣ □ are not invertible;
   - the counit ε' : ◇∇ ⇒ 1_Disc of ◇ ⊣ ∇ is an isomorphism (i.e. ∇ is fully faithful), while its unit η' : 1_Type ⇒ ∇◇ is not;
   - ◇△ ≅ 1_Disc, and hence (passing to right adjoints of the composable pairs △ ⊣ □ and ◇ ⊣ ∇) also □∇ ≅ 1_Disc.

   The isomorphisms induce 2-cells between the parallel generators:

     ι : □ ⇒ ◇   as   □ = □∘1 ⇒ □∘(∇◇) = (□∇)∘◇ ≅ ◇     (whiskered η', then whiskered □∇ ≅ 1)
     κ : △ ⇒ ∇   as   △ = 1∘△ ⇒ (∇◇)∘△ = ∇∘(◇△) ≅ ∇     (whiskered η', then whiskered ◇△ ≅ 1)

   Every modality is isomorphic to exactly one normal form: an alternating word in △ and □, optionally with a single ◇ at the source end (the first generator applied, displayed at the right in applicative notation) and/or a single ∇ at the target end (displayed at the left).  The reductions performed by normalization are exactly the three isomorphisms, each of which cancels an adjacent pair of generators in application order: (∇, ◇) by ε', (△, ◇) by ◇△ ≅ 1, and (∇, □) by □∇ ≅ 1.  Cancelling the source-most pair of a word whose tail is normal leaves a normal word, so normalization proceeds one generator at a time with no cascading.

   Like the walking adjunction (see adjunction.ml), this theory is not locally posetal, and a 2-cell is uniquely determined by the pairing it induces on the generators of its domain and codomain words.  In addition to the arcs and strands of the walking adjunction, a unit η' pairs the (◇, ∇) in its codomain, the isomorphisms and their formal inverses pair the two generators of their domain or codomain, and the induced cells ι and κ produce through-strands connecting a □ in the domain to a ◇ in the codomain, or a △ to a ∇.  Unlike the walking adjunction, closed loops CAN arise when composing pairings vertically -- exactly when an isomorphism cancels its formal inverse -- and are dropped.

   Between two *normal forms* m and n, the possible pairings are as follows.

   - Domain arcs connect an adjacent (in application order) pair (□, △) of m, killed by a counit ε.  As in the walking adjunction, arcs connecting non-adjacent generators are impossible: an arc encloses no through-strands, by planarity, so an innermost arc connects adjacent generators, and no domain arc can sit immediately inside another (removing an adjacent (□, △) creates only new adjacencies (△, □) and (△, ∇), neither of which is killable, since neither □∘△ ⇒ 1 nor ∇∘△ ⇒ 1 exists).  The other killable pairs (∇, ◇), (△, ◇), and (∇, □) never occur in a normal form.

   - Codomain arcs connect an adjacent pair (△, □) of n, created by a unit η; or the initial ◇ and final ∇ of n, created by a unit η', provided everything in between -- necessarily of the form (△□)^k -- is created by η's nested directly inside (removing adjacent (△, □) pairs creates only the new adjacency (◇, ∇), so the only possible nesting is a single (◇, ∇) arc over a tiling by (△, □) arcs).  The creatable pairs (∇, ◇), (△, ◇), and (∇, □) (inverses of the isomorphisms) never occur in a normal form.

   - Through-strands connect the remaining generators of m and n in order; each strand connects two equal generators, or a □ to a ◇ (the cell ι), or a △ to a ∇ (the cell κ).  Note that a (◇, ∇) codomain arc spans the whole of n, so it can occur only when m is entirely killed by domain arcs.

   The enumeration in [count] below recurses on the source ends of the two words by case analysis on the fate of the source-most generator of m (killed by ε, or passed through after stripping unit-created arcs from the source end of n), together with the (◇, ∇) cap when m is exhausted; each pairing corresponds to exactly one recursion trace, so none is counted twice. *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
  val locker : bool
  val nabla_tangible : bool
  val tri_pellucid : bool
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "adjunction"
  let locker = false
  let nabla_tangible = true
  let tri_pellucid = false
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete adjunction"
  let locker = true
  let nabla_tangible = false
  let tri_pellucid = true
end

module DiscGen (V : Variant) = struct
  let name = ref "Disc"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module TypeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TriangleGen
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Disc.t
  type tgt = Type.t

  let src = Disc.mode
  let tgt = Type.mode
  let name = ref "△"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module BoxGen
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Type.t
  type tgt = Disc.t

  let src = Type.mode
  let tgt = Disc.mode
  let name = ref "□"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module DiamondGen
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Type.t
  type tgt = Disc.t

  let src = Type.mode
  let tgt = Disc.mode
  let name = ref "◇"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module NablaGen
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Disc.t
  type tgt = Type.t

  let src = Disc.mode
  let tgt = Type.mode
  let name = ref "∇"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module GwptCells
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen)
    (Triangle : Modality.Generated with module G := TriangleGen(V)(Disc)(Type))
    (Box : Modality.Generated with module G := BoxGen(V)(Disc)(Type))
    (Diamond : Modality.Generated with module G := DiamondGen(V)(Disc)(Type))
    (Nabla : Modality.Generated with module G := NablaGen(V)(Disc)(Type)) =
struct
  let disc = Disc.mode
  let typ = Type.mode

  (* The four generating modalities. *)
  let tri = Modality.of_gen Triangle.modality
  let box = Modality.of_gen Box.modality
  let dia = Modality.of_gen Diamond.modality
  let nab = Modality.of_gen Nabla.modality

  (* The two-generator composite modalities.  A modality Path (Suc (Suc (Zero, X), Y), tgt) applies Y first (source side) and then X, i.e. it is X ∘ Y. *)
  let tribox = Modality.Path (Suc (Suc (Zero, Triangle.modality), Box.modality), typ)
  let boxtri = Modality.Path (Suc (Suc (Zero, Box.modality), Triangle.modality), disc)
  let nabdia = Modality.Path (Suc (Suc (Zero, Nabla.modality), Diamond.modality), typ)
  let dianab = Modality.Path (Suc (Suc (Zero, Diamond.modality), Nabla.modality), disc)
  let diatri = Modality.Path (Suc (Suc (Zero, Diamond.modality), Triangle.modality), disc)
  let boxnab = Modality.Path (Suc (Suc (Zero, Box.modality), Nabla.modality), disc)
  let tridia = Modality.Path (Suc (Suc (Zero, Triangle.modality), Diamond.modality), typ)
  let nabbox = Modality.Path (Suc (Suc (Zero, Nabla.modality), Box.modality), typ)

  (* The generating 2-cells (source ⇒ target).  The three isomorphisms get explicit formal inverses; when composing pairings, an inverse cancelling its isomorphism produces a closed loop, which is dropped.
       tb_unit : 1_Disc ⇒ □△                 tb_counit : △□ ⇒ 1_Type
       dn_unit : 1_Type ⇒ ∇◇                 dn_counit : ◇∇ ⇒ 1_Disc (iso)
       dt_iso : ◇△ ⇒ 1_Disc (iso)            bn_iso : □∇ ⇒ 1_Disc (iso)
       box_dia : □ ⇒ ◇                       tri_nab : △ ⇒ ∇

     We have to be more careful in choosing the names of these cells than we would in a locally posetal theory, because the user may need to refer to them in manual key operations.  And since there are multiple adjunctions around, we can't just call them η and ε.  We choose to name them by their source and target with a ⇨ between. *)
  let tb_unit_gen = Modalcell.generate "1⇨□△" (Modality.id disc) boxtri
  let tb_counit_gen = Modalcell.generate "△□⇨1" tribox (Modality.id typ)
  let dn_unit_gen = Modalcell.generate "1⇨∇◇" (Modality.id typ) nabdia
  let dn_counit_gen = Modalcell.generate "◇∇⇨1" dianab (Modality.id disc)
  let dn_counit_inv_gen = Modalcell.generate "1⇨◇∇" (Modality.id disc) dianab
  let dt_iso_gen = Modalcell.generate "◇△⇨1" diatri (Modality.id disc)
  let dt_iso_inv_gen = Modalcell.generate "1⇨◇△" (Modality.id disc) diatri
  let bn_iso_gen = Modalcell.generate "□∇⇨1" boxnab (Modality.id disc)
  let bn_iso_inv_gen = Modalcell.generate "1⇨□∇" (Modality.id disc) boxnab
  let box_dia_gen = Modalcell.generate "□⇨◇" box dia
  let tri_nab_gen = Modalcell.generate "△⇨∇" tri nab
  let tb_unit = Modalcell.of_gen tb_unit_gen
  let tb_counit = Modalcell.of_gen tb_counit_gen
  let dn_unit = Modalcell.of_gen dn_unit_gen
  let dn_counit = Modalcell.of_gen dn_counit_gen
  let dn_counit_inv = Modalcell.of_gen dn_counit_inv_gen
  let dt_iso = Modalcell.of_gen dt_iso_gen
  let dt_iso_inv = Modalcell.of_gen dt_iso_inv_gen
  let bn_iso = Modalcell.of_gen bn_iso_gen
  let bn_iso_inv = Modalcell.of_gen bn_iso_inv_gen
  let box_dia = Modalcell.of_gen box_dia_gen
  let tri_nab = Modalcell.of_gen tri_nab_gen

  (* The pairing induced by each generating 2-cell: a unit (or the inverse of an isomorphism) pairs the two generators of its codomain, a counit (or an isomorphism) pairs the two generators of its domain, and the induced cells ι and κ pair their source with their target. *)
  let gen_pairs : type a m n b. (a, m, n, b) Modalcell.Gen.t -> (endpoint * endpoint) list =
   fun g ->
    let is : type a2 m2 n2 b2. (a2, m2, n2, b2) Modalcell.Gen.t -> bool =
     fun c ->
      match Modalcell.Gen.compare g c with
      | Eq -> true
      | Neq -> false in
    if
      is tb_unit_gen
      || is dn_unit_gen
      || is dn_counit_inv_gen
      || is dt_iso_inv_gen
      || is bn_iso_inv_gen
    then [ (Cod 0, Cod 1) ]
    else if is tb_counit_gen || is dn_counit_gen || is dt_iso_gen || is bn_iso_gen then
      [ (Dom 0, Dom 1) ]
    else if is box_dia_gen || is tri_nab_gen then [ (Dom 0, Cod 0) ]
    else failwith "unrecognized generating 2-cell in gwpt mode theory"

  let pairing c = Pairing.of_pairs (Pairing.of_cell ~allow_loops:true { gen_pairs } c)

  (* Two parallel 2-cells are equal exactly when they induce the same pairing. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun c1 c2 -> Pairing.equal (pairing c1) (pairing c2)

  (* The composite adjunction △◇ ⊣ ∇□, whose unit and counit are built out of those of the generating adjunctions:
       tridia_unit : 1_Type ⇒ ∇□△◇ is η' with an η inserted in the middle (next to the ◇);
       tridia_counit : △◇∇□ ⇒ 1_Type is ε' applied in the middle (next to the □) followed by ε. *)
  let tridia_unit =
    Modalcell.vcomp
      (Modalcell.hcomp
         (Suc (Zero, Diamond.modality))
         (Suc (Suc (Suc (Zero, Box.modality), Triangle.modality), Diamond.modality))
         (Modalcell.id nab)
         (Modalcell.hcomp
            (Suc (Zero, Diamond.modality))
            (Suc (Zero, Diamond.modality))
            tb_unit (Modalcell.id dia)))
      dn_unit

  let tridia_counit =
    Modalcell.vcomp tb_counit
      (Modalcell.hcomp
         (Suc (Suc (Suc (Zero, Diamond.modality), Nabla.modality), Box.modality))
         (Suc (Zero, Box.modality))
         (Modalcell.id tri)
         (Modalcell.hcomp
            (Suc (Zero, Box.modality))
            (Suc (Zero, Box.modality))
            dn_counit (Modalcell.id box)))

  (* A modality is sinister (a declared left adjoint) if it is an identity, △ (left adjoint to □), ◇ (left adjoint to ∇), or the composite △◇ (left adjoint to ∇□). *)
  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match
      ( Modality.compare_id f,
        Modality.compare f tri,
        Modality.compare f dia,
        Modality.compare f tridia )
    with
    | Eq, _, _, _ -> Some (Modalcell.id_sinister (Modality.src f))
    | _, Eq, _, _ ->
        (* △ ⊣ □ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = tri;
                  right = box;
                  right_left = Suc (Zero, Triangle.modality);
                  unit = tb_unit;
                  left_right = Suc (Zero, Box.modality);
                  counit = tb_counit;
                }))
    | _, _, Eq, _ ->
        (* ◇ ⊣ ∇ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = dia;
                  right = nab;
                  right_left = Suc (Zero, Diamond.modality);
                  unit = dn_unit;
                  left_right = Suc (Zero, Nabla.modality);
                  counit = dn_counit;
                }))
    | _, _, _, Eq ->
        (* △◇ ⊣ ∇□ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = tridia;
                  right = nabbox;
                  right_left = Suc (Suc (Zero, Triangle.modality), Diamond.modality);
                  unit = tridia_unit;
                  left_right = Suc (Suc (Zero, Nabla.modality), Box.modality);
                  counit = tridia_counit;
                }))
    | _ -> None

  (* The normalization of a modality: an isomorphic normal form together with the isomorphism (in both directions).  Every modality is isomorphic to exactly one normal form. *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  (* Prepend a generator g (on the source side, i.e. applied first) to an already-normalized modality, and renormalize.  The reductions are the three isomorphisms, each of which cancels g together with the source-most generator h of nf: (g, h) = (∇, ◇) by ε', (△, ◇) by dt_iso, or (∇, □) by bn_iso.  A reduction removes the source-most generator of a normal form, leaving a normal form, so no further reduction fires; and if no reduction fires, then g·nf is itself normal.  We are given the isomorphisms g·rest ⇒ g·nf (g_to) and g·nf ⇒ g·rest (g_from) obtained by prewhiskering the sub-isomorphisms by g, and we postcompose the whiskered reduction cell. *)
  let prepend : type c gg a nf b gm.
      (c, gg, a) Modality.Gen.t ->
      (a, nf, b) Modality.t ->
      (c, gm, (nf, gg) Modality.suc, b) Modalcell.t ->
      (c, (nf, gg) Modality.suc, gm, b) Modalcell.t ->
      (c, gm, b) normalize =
   fun g nf g_to g_from ->
    match nf with
    | Path (Zero, _) -> Normalize (Modality.suc nf g, g_to, g_from)
    | Path (Suc (inner, h), nb) -> (
        let rest = Modality.Path (inner, nb) in
        match
          ( Modality.Gen.compare g Triangle.modality,
            Modality.Gen.compare g Nabla.modality,
            Modality.Gen.compare h Diamond.modality,
            Modality.Gen.compare h Box.modality )
        with
        | Eq, _, Eq, _ ->
            (* ◇∘△ ≅ 1_Disc *)
            let kill =
              Modalcell.hcomp
                (Suc (Suc (Zero, Diamond.modality), Triangle.modality))
                Zero (Modalcell.id rest) dt_iso in
            let unkill =
              Modalcell.hcomp Zero
                (Suc (Suc (Zero, Diamond.modality), Triangle.modality))
                (Modalcell.id rest) dt_iso_inv in
            Normalize (rest, Modalcell.vcomp kill g_to, Modalcell.vcomp g_from unkill)
        | _, Eq, Eq, _ ->
            (* ◇∘∇ ≅ 1_Disc *)
            let kill =
              Modalcell.hcomp
                (Suc (Suc (Zero, Diamond.modality), Nabla.modality))
                Zero (Modalcell.id rest) dn_counit in
            let unkill =
              Modalcell.hcomp Zero
                (Suc (Suc (Zero, Diamond.modality), Nabla.modality))
                (Modalcell.id rest) dn_counit_inv in
            Normalize (rest, Modalcell.vcomp kill g_to, Modalcell.vcomp g_from unkill)
        | _, Eq, _, Eq ->
            (* □∘∇ ≅ 1_Disc *)
            let kill =
              Modalcell.hcomp
                (Suc (Suc (Zero, Box.modality), Nabla.modality))
                Zero (Modalcell.id rest) bn_iso in
            let unkill =
              Modalcell.hcomp Zero
                (Suc (Suc (Zero, Box.modality), Nabla.modality))
                (Modalcell.id rest) bn_iso_inv in
            Normalize (rest, Modalcell.vcomp kill g_to, Modalcell.vcomp g_from unkill)
        | _ -> Normalize (Modality.suc nf g, g_to, g_from))

  let rec normalize : type a m b. (a, m, b) Modality.t -> (a, m, b) normalize =
   fun md ->
    match md with
    | Path (Zero, mode) -> Normalize (Modality.id mode, Modalcell.id2 mode, Modalcell.id2 mode)
    | Path (Suc (inner, g), tgt) ->
        let (Normalize (nf, to_nf, from_nf)) = normalize (Path (inner, tgt)) in
        let g_to = Modalcell.prewhisker (Suc (Zero, g)) (Suc (Zero, g)) to_nf (Modality.of_gen g) in
        let g_from =
          Modalcell.prewhisker (Suc (Zero, g)) (Suc (Zero, g)) from_nf (Modality.of_gen g) in
        prepend g nf g_to g_from

  (* Count the 2-cells between two normal forms, cutting off at two, and construct the cell if there is exactly one. *)
  type (_, _, _, _) count =
    | Zero_cells : ('a, 'm, 'n, 'b) count
    | One_cell : ('a, 'm, 'n, 'b) Modalcell.t -> ('a, 'm, 'n, 'b) count
    | Many_cells : ('a, 'm, 'n, 'b) count

  let add_count : type a m n b. (a, m, n, b) count -> (a, m, n, b) count -> (a, m, n, b) count =
   fun x y ->
    match (x, y) with
    | Zero_cells, y -> y
    | x, Zero_cells -> x
    | _ -> Many_cells

  (* Build the cell 1_Type ⇒ rest∘◇, where rest is required to have the normal form ∇∘(□△)^k (otherwise return None): the unit η' : 1 ⇒ ∇◇, with k units η inserted next to the ◇. *)
  let rec cap : type r.
      (Disc.t, r, Type.t) Modality.t ->
      (Type.t, Type.t Modality.id, (r, Diamond.t) Modality.suc, Type.t) Modalcell.t option =
   fun rest ->
    match rest with
    | Path (Suc (Zero, h), _) -> (
        match Modality.Gen.compare h Nabla.modality with
        | Eq -> Some dn_unit
        | Neq -> None)
    | Path (Suc (Suc (inner, h2), h1), nb) -> (
        match (Modality.Gen.compare h1 Triangle.modality, Modality.Gen.compare h2 Box.modality) with
        | Eq, Eq -> (
            let rest2 = Modality.Path (inner, nb) in
            match cap rest2 with
            | Some c ->
                (* insert : rest2∘◇ ⇒ rest2∘(□△)∘◇ *)
                let insert =
                  Modalcell.hcomp
                    (Suc (Zero, Diamond.modality))
                    (Suc (Suc (Suc (Zero, Box.modality), Triangle.modality), Diamond.modality))
                    (Modalcell.id rest2)
                    (Modalcell.hcomp
                       (Suc (Zero, Diamond.modality))
                       (Suc (Zero, Diamond.modality))
                       tb_unit (Modalcell.id dia)) in
                Some (Modalcell.vcomp insert c)
            | None -> None)
        | _ -> None)
    | _ -> None

  (* The enumeration recurses on the source (first-applied) ends of the two normal-form words, following the combinatorial description of pairings given at the top of the file.  Each pairing is counted exactly once, by case analysis on the fate of the source-most generator of m. *)
  let rec count : type a m n b. (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) count =
   fun m n ->
    (* First alternative: the source-most generator of m is killed by a counit ε.  It can only be paired with the generator adjacent to it, so m must begin (in application order) with (□, △), i.e. m = m'' ∘ △□; and the cell factors as a counit at the source end of m followed by a cell m'' ⇒ n. *)
    let kills : (a, m, n, b) count =
      match m with
      | Path (Suc (Suc (ev, g2), g1), mb) -> (
          match
            (Modality.Gen.compare g1 Box.modality, Modality.Gen.compare g2 Triangle.modality)
          with
          | Eq, Eq -> (
              let m'' = Modality.Path (ev, mb) in
              match count m'' n with
              | Zero_cells -> Zero_cells
              | Many_cells -> Many_cells
              | One_cell c ->
                  let kill =
                    Modalcell.hcomp
                      (Suc (Suc (Zero, Triangle.modality), Box.modality))
                      Zero (Modalcell.id m'') tb_counit in
                  One_cell (Modalcell.vcomp c kill))
          | _ -> Zero_cells)
      | _ -> Zero_cells in
    (* Second alternative: the source-most generator of m (if any) passes straight through to n, possibly converted by ι : □ ⇒ ◇ or κ : △ ⇒ ∇.  Then all the generators of n on the source side of its partner must be paired among themselves, forming unit-created adjacent (△, □) pairs tiling the source end of n.  So we strip zero or more such pairs from n, and then either pair up the source-most generators of m and the stripped n and recurse, or finish.  Finishing requires the stripped n to be empty, or -- if m is also empty -- to consist of a single (◇, ∇) arc created by η' over a tiling by η's, built by [cap].  The wrap argument turns a cell targeting the stripped n back into one targeting n, by vertically composing with the unit cells that create the stripped pairs. *)
    let rec strip : type nk.
        (a, nk, b) Modality.t ->
        ((a, m, nk, b) Modalcell.t -> (a, m, n, b) Modalcell.t) ->
        (a, m, n, b) count =
     fun nk wrap ->
      let here : (a, m, n, b) count =
        match (m, nk) with
        | Path (Zero, _), Path (Zero, _) -> One_cell (wrap (Modalcell.id m))
        | Path (Zero, _), Path (Suc (nev, h), nb) -> (
            (* The (◇, ∇) cap spans the whole of the remaining codomain, so it can only occur when m is exhausted. *)
            match Modality.Gen.compare h Diamond.modality with
            | Eq -> (
                match cap (Modality.Path (nev, nb)) with
                | Some c -> One_cell (wrap c)
                | None -> Zero_cells)
            | Neq -> Zero_cells)
        | Path (Suc (mev, g), mb), Path (Suc (nev, h), nb) -> (
            let m' = Modality.Path (mev, mb) in
            let nk' = Modality.Path (nev, nb) in
            match Modality.Gen.compare g h with
            | Eq -> (
                match count m' nk' with
                | Zero_cells -> Zero_cells
                | Many_cells -> Many_cells
                | One_cell c ->
                    One_cell
                      (wrap
                         (Modalcell.hcomp
                            (Suc (Zero, g))
                            (Suc (Zero, g))
                            c
                            (Modalcell.id (Modality.of_gen g)))))
            | Neq -> (
                match
                  ( Modality.Gen.compare g Box.modality,
                    Modality.Gen.compare h Diamond.modality,
                    Modality.Gen.compare g Triangle.modality,
                    Modality.Gen.compare h Nabla.modality )
                with
                | Eq, Eq, _, _ -> (
                    (* ι : □ ⇒ ◇ *)
                    match count m' nk' with
                    | Zero_cells -> Zero_cells
                    | Many_cells -> Many_cells
                    | One_cell c ->
                        One_cell
                          (wrap
                             (Modalcell.hcomp
                                (Suc (Zero, Box.modality))
                                (Suc (Zero, Diamond.modality))
                                c box_dia)))
                | _, _, Eq, Eq -> (
                    (* κ : △ ⇒ ∇ *)
                    match count m' nk' with
                    | Zero_cells -> Zero_cells
                    | Many_cells -> Many_cells
                    | One_cell c ->
                        One_cell
                          (wrap
                             (Modalcell.hcomp
                                (Suc (Zero, Triangle.modality))
                                (Suc (Zero, Nabla.modality))
                                c tri_nab)))
                | _ -> Zero_cells))
        | _ -> Zero_cells in
      let deeper : (a, m, n, b) count =
        match nk with
        | Path (Suc (Suc (nev, g2), g1), nb) -> (
            match
              (Modality.Gen.compare g1 Triangle.modality, Modality.Gen.compare g2 Box.modality)
            with
            | Eq, Eq ->
                let n1 = Modality.Path (nev, nb) in
                let create =
                  Modalcell.hcomp Zero
                    (Suc (Suc (Zero, Box.modality), Triangle.modality))
                    (Modalcell.id n1) tb_unit in
                strip n1 (fun c -> wrap (Modalcell.vcomp create c))
            | _ -> Zero_cells)
        | _ -> Zero_cells in
      add_count here deeper in
    add_count kills (strip n (fun c -> c))

  (* A 2-cell can be inserted as an implicit key only when it is unique; if there are several parallel cells, the user must disambiguate.  We normalize both modalities, count the cells between the normal forms, and compose with the normalization isomorphisms. *)
  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let (Normalize (_, xto, _)) = normalize x in
    let (Normalize (_, _, yfrom)) = normalize y in
    match count (Modalcell.vtgt xto) (Modalcell.vsrc yfrom) with
    | One_cell c -> Some (Modalcell.vcomp (Modalcell.vcomp yfrom c) xto)
    | Zero_cells | Many_cells -> None

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun m ->
    if V.locker then
      match Mode.compare m Type.mode with
      | Eq -> Ok (Modalcell.Locker (tribox, tb_counit))
      | Neq -> Ok (Locker (Modality.id m, Id (Modality.id m)))
    else Error "gwpt"

  (* Since parallel 2-cells can differ, we display a cell by its pairing. *)
  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun c -> Pairing.to_string (Pairing.of_cell ~allow_loops:true { gen_pairs } c)

  (* The theory of modality properties is nested inside the cells module, so that installing both theories instantiates this functor -- and in particular Modalcell.generate, which allocates fresh generating 2-cells -- only once. *)
  module Modalities : Modality.Theory = struct
    (* The left adjoints (those whose normal forms contain no □ or ∇, namely the identities, △, ◇, and △◇) are transparent. *)
    let rec transparent_normal : type a m b. (a, m, b) Modality.t -> bool = function
      | Path (Zero, _) -> true
      | Path (Suc (m, g), mode) -> (
          match (Modality.Gen.compare g Box.modality, Modality.Gen.compare g Nabla.modality) with
          | Eq, _ | _, Eq -> false
          | Neq, Neq -> transparent_normal (Path (m, mode)))

    let transparent m =
      let (Normalize (m, _, _)) = normalize m in
      transparent_normal m

    (* In the discrete case, ∇ is not tangible or translucent, so that it doesn't become discrete (it should be codiscrete).  Since ◇ has no left adjoint, this means there is no way to define a composed modal operator ∇◇ directly, only a positive ◇ and a negative ∇.  *)
    let tangible : type a m b. (a, m, b) Modality.t -> bool =
     fun m ->
      match Modality.compare m nab with
      | Eq -> V.nabla_tangible
      | Neq -> true

    let translucent m = tangible m

    (* In the discrete case, where we have a specific semantics in mind, △ is pellucid since it has a left adjoint, so is the inverse image of a locally connected geometric morphism.  In the additionally external case, the semantics is in *(EI-)inverse* diagrams with ◇ being evaluation at 0, so it is pellucid, hence so is the composite ◇△. *)
    let pellucid : type a m b. (a, m, b) Modality.t -> bool =
     fun m ->
      if V.tri_pellucid then
        if Endpoints.internal () then
          match Modality.compare m tri with
          | Eq -> true
          | Neq -> false
        else transparent m
      else false
  end
end

let install (module V : Variant) modes modalities =
  let module Disc = DiscGen (V) in
  (match modes with
  | [ disc; ty ] ->
      Disc.name := disc;
      TypeGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for gwpt mode theory");
  let module Disc = Mode.Generate (Disc) in
  let module Type = Mode.Generate (TypeGen) in
  let module Tri = TriangleGen (V) (Disc) (Type) in
  let module Bx = BoxGen (V) (Disc) (Type) in
  let module Dia = DiamondGen (V) (Disc) (Type) in
  let module Nab = NablaGen (V) (Disc) (Type) in
  (match modalities with
  | [ tri; box; dia; nab ] ->
      Tri.name := tri;
      Bx.name := box;
      Dia.name := dia;
      Nab.name := nab
  | [] -> ()
  | _ -> failwith "wrong number of modality names for gwpt mode theory");
  Modality.set_one_char true modalities;
  let module Triangle = Modality.Generate (Tri) in
  let module Box = Modality.Generate (Bx) in
  let module Diamond = Modality.Generate (Dia) in
  let module Nabla = Modality.Generate (Nab) in
  let module Cells = GwptCells (V) (Disc) (Type) (Triangle) (Box) (Diamond) (Nabla) in
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
