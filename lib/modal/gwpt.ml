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

   Like the walking adjunction (see adjunction.ml), this theory is not locally posetal, and a 2-cell between normal forms is uniquely determined by the pairing it induces on the generators of its domain and codomain words.  In addition to the arcs and strands of the walking adjunction, a unit η' pairs the (◇, ∇) in its codomain, the isomorphisms and their formal inverses pair the two generators of their domain or codomain, and the induced cells ι and κ produce through-strands connecting a □ in the domain to a ◇ in the codomain, or a △ to a ∇.  Unlike the walking adjunction, closed loops CAN arise when composing pairings vertically -- exactly when an isomorphism cancels its formal inverse -- and are dropped.

   Between two *normal forms* m and n, the possible pairings are as follows.

   - Domain arcs connect a pair (□, △) of m (in application order), killed by a counit ε, or a pair (△, □), killed by converting the □ to a ◇ with ι and then using ◇△ ≅ 1 (or equivalently, converting the △ to a ∇ with κ and using □∇ ≅ 1).  An arc encloses no through-strands, by planarity, so the generators inside it are killed by arcs nested inside it, after which the ends of the arc become adjacent; since both kinds of pair can be killed, arcs can be nested arbitrarily.  The other killable pairs (∇, ◇), (△, ◇), and (∇, □) never occur in a normal form, even after killing what is between them, since ◇ and ∇ can only occur at its ends.

   - Codomain arcs connect an adjacent pair (△, □) of n, created by a unit η; or the initial ◇ and final ∇ of n, created by a unit η', provided everything in between -- necessarily of the form (△□)^k -- is created by η's nested directly inside (removing adjacent (△, □) pairs creates only the new adjacency (◇, ∇), so the only possible nesting is a single (◇, ∇) arc over a tiling by (△, □) arcs).  The creatable pairs (∇, ◇), (△, ◇), and (∇, □) (inverses of the isomorphisms) never occur in a normal form.

   - Through-strands connect the remaining generators of m and n in order; each strand connects two equal generators, or a □ to a ◇ (the cell ι), or a △ to a ∇ (the cell κ).  Note that a (◇, ∇) codomain arc spans the whole of n, so it can occur only when m is entirely killed by domain arcs.

   The enumeration in [Enumerate] below recurses on the source ends of the two words by case analysis on the fate of the source-most generator of m (killed by an arc, with everything inside the arc killed, or passed through after stripping unit-created arcs from the source end of n), together with the (◇, ∇) cap when m is exhausted; each pairing corresponds to exactly one recursion trace, so none is found twice.  (This is checked, up to a given length, by the test in test/white/modal_closure.ml.) *)

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

  (* Two parallel 2-cells between normal forms are equal exactly when they induce the same pairing.  Between other modalities this isn't true, since for instance an isomorphism followed by its inverse pairs the generators of its domain and of its codomain among themselves rather than with each other; so we first conjugate the cells by the normalizations of their source and target, which is a bijection onto the cells between the normal forms. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun c1 c2 ->
    let (Normalize (_, _, xfrom)) = normalize (Modalcell.vsrc c1) in
    let (Normalize (_, yto, _)) = normalize (Modalcell.vtgt c1) in
    let conj c = Modalcell.vcomp yto (Modalcell.vcomp c xfrom) in
    Pairing.equal (pairing (conj c1)) (pairing (conj c2))

  (* A way of collecting the 2-cells between two normal forms found by the enumeration below: counting them, or listing them. *)
  module type Collection = sig
    type ('a, 'm, 'n, 'b) t

    val zero : ('a, 'm, 'n, 'b) t
    val one : ('a, 'm, 'n, 'b) Modalcell.t -> ('a, 'm, 'n, 'b) t
    val add : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'n, 'b) t -> ('a, 'm, 'n, 'b) t

    val map :
      (('a, 'm, 'k, 'b) Modalcell.t -> ('c, 'p, 'q, 'd) Modalcell.t) ->
      ('a, 'm, 'k, 'b) t ->
      ('c, 'p, 'q, 'd) t
  end

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

  (* A modality consisting of a single generator. *)
  type (_, _, _) single =
    | Single : ('x, 'g, 'y) Modality.Gen.t -> ('x, ('y Modality.id, 'g) Modality.suc, 'y) single

  let single : type x r y. (x, r, y) Modality.t -> (x, r, y) single option = function
    | Path (Suc (Zero, g), _) -> Some (Single g)
    | _ -> None

  (* The counit of △ ⊣ □ kills an adjacent (□, △), in application order; and an adjacent (△, □) can also be killed, by converting the □ to a ◇ with ι and then using ◇△ ≅ 1. *)
  let tb_kill =
    Modalcell.vcomp dt_iso
      (Modalcell.hcomp
         (Suc (Zero, Triangle.modality))
         (Suc (Zero, Triangle.modality))
         box_dia (Modalcell.id tri))

  (* All the cells w ⇒ id that kill all of a word w by (necessarily nested) arcs, and those in which, moreover, the first and last generators of w are paired with each other. *)
  let rec kill_all : type a m. (a, m, a) Modality.t -> (a, m, a Modality.id, a) Modalcell.t list =
   fun w ->
    match w with
    | Path (Zero, _) -> [ Modalcell.id w ]
    | Path (Suc _, _) ->
        let per_split : (a, m, a) Modality.split -> (a, m, a Modality.id, a) Modalcell.t list =
         fun (Modality.Split (p, r, ev)) ->
          if Modality.length p = 0 then []
          else
            match Mode.compare (Modality.src p) (Modality.tgt p) with
            | Neq -> []
            | Eq ->
                List.concat_map
                  (fun cp ->
                    List.map
                      (fun cr -> Modalcell.vcomp cr (Modalcell.hcomp ev Zero (Modalcell.id r) cp))
                      (kill_all r))
                  (arc_cells p) in
        List.concat_map per_split (Modality.splits w)

  and arc_cells : type a m. (a, m, a) Modality.t -> (a, m, a Modality.id, a) Modalcell.t list =
   fun p -> List.concat_map arc_with_last (Modality.splits p)

  (* Writing p as h ∘ i ∘ g with h and g single generators: first h, ... *)
  and arc_with_last : type a m.
      (a, m, a) Modality.split -> (a, m, a Modality.id, a) Modalcell.t list =
   fun (Modality.Split (pre, h, eva)) ->
    match single h with
    | None -> []
    | Some (Single hg) -> List.concat_map (arc_with_first h hg eva) (Modality.splits pre)

  (* ... and then g. *)
  and arc_with_first : type a pm x hg m.
      (x, (a Modality.id, hg) Modality.suc, a) Modality.t ->
      (x, hg, a) Modality.Gen.t ->
      (a, pm, x, (a Modality.id, hg) Modality.suc, a, m) Modality.comp ->
      (a, pm, x) Modality.split ->
      (a, m, a Modality.id, a) Modalcell.t list =
   fun h hg eva (Modality.Split (g, i, evg)) ->
    match single g with
    | None -> []
    | Some (Single gg) -> (
        match Mode.compare (Modality.src i) (Modality.tgt i) with
        | Neq -> []
        | Eq -> (
            (* Kill the inside, leaving the first and last generators adjacent, and then kill them. *)
            let inside ci =
              Modalcell.hcomp eva
                (Suc (Zero, gg))
                (Modalcell.id h)
                (Modalcell.hcomp evg (Suc (Zero, gg)) ci (Modalcell.id g)) in
            match
              ( Modality.Gen.compare gg Box.modality,
                Modality.Gen.compare hg Triangle.modality,
                Modality.Gen.compare gg Triangle.modality,
                Modality.Gen.compare hg Box.modality )
            with
            | Eq, Eq, _, _ ->
                List.map (fun ci -> Modalcell.vcomp tb_counit (inside ci)) (kill_all i)
            | _, _, Eq, Eq -> List.map (fun ci -> Modalcell.vcomp tb_kill (inside ci)) (kill_all i)
            | _ -> []))

  (* The enumeration recurses on the source (first-applied) ends of the two normal-form words, following the combinatorial description of pairings given at the top of the file.  Each pairing is found exactly once, by case analysis on the fate of the source-most generator of m. *)
  module Enumerate (C : Collection) = struct
    let rec cells : type a m n b. (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) C.t =
     fun m n ->
      (* First alternative: the source-most generator of m is killed by an arc, whose other end is the last generator of some prefix p of m, with everything inside it killed (see arc_cells); and the cell factors as such a cell p ⇒ 1 at the source end of m followed by a cell from the rest of m to n. *)
      let kills : (a, m, n, b) C.t =
        let per_split : (a, m, n, b) C.t -> (a, m, b) Modality.split -> (a, m, n, b) C.t =
         fun acc (Split (p, r, ev)) ->
          if Modality.length p = 0 then acc
          else
            match Mode.compare (Modality.src p) (Modality.tgt p) with
            | Neq -> acc
            | Eq ->
                List.fold_left
                  (fun acc cp ->
                    C.add acc
                      (C.map
                         (fun c -> Modalcell.vcomp c (Modalcell.hcomp ev Zero (Modalcell.id r) cp))
                         (cells r n)))
                  acc (arc_cells p) in
        List.fold_left per_split C.zero (Modality.splits m) in
      let rec strip : type nk.
          (a, nk, b) Modality.t ->
          ((a, m, nk, b) Modalcell.t -> (a, m, n, b) Modalcell.t) ->
          (a, m, n, b) C.t =
       fun nk wrap ->
        let here : (a, m, n, b) C.t =
          match (m, nk) with
          | Path (Zero, _), Path (Zero, _) -> C.one (wrap (Modalcell.id m))
          | Path (Zero, _), Path (Suc (nev, h), nb) -> (
              (* The (◇, ∇) cap spans the whole of the remaining codomain, so it can only occur when m is exhausted. *)
              match Modality.Gen.compare h Diamond.modality with
              | Eq -> (
                  match cap (Modality.Path (nev, nb)) with
                  | Some c -> C.one (wrap c)
                  | None -> C.zero)
              | Neq -> C.zero)
          | Path (Suc (mev, g), mb), Path (Suc (nev, h), nb) -> (
              let m' = Modality.Path (mev, mb) in
              let nk' = Modality.Path (nev, nb) in
              match Modality.Gen.compare g h with
              | Eq ->
                  C.map
                    (fun c ->
                      wrap
                        (Modalcell.hcomp
                           (Suc (Zero, g))
                           (Suc (Zero, g))
                           c
                           (Modalcell.id (Modality.of_gen g))))
                    (cells m' nk')
              | Neq -> (
                  match
                    ( Modality.Gen.compare g Box.modality,
                      Modality.Gen.compare h Diamond.modality,
                      Modality.Gen.compare g Triangle.modality,
                      Modality.Gen.compare h Nabla.modality )
                  with
                  | Eq, Eq, _, _ ->
                      (* ι : □ ⇒ ◇ *)
                      C.map
                        (fun c ->
                          wrap
                            (Modalcell.hcomp
                               (Suc (Zero, Box.modality))
                               (Suc (Zero, Diamond.modality))
                               c box_dia))
                        (cells m' nk')
                  | _, _, Eq, Eq ->
                      (* κ : △ ⇒ ∇ *)
                      C.map
                        (fun c ->
                          wrap
                            (Modalcell.hcomp
                               (Suc (Zero, Triangle.modality))
                               (Suc (Zero, Nabla.modality))
                               c tri_nab))
                        (cells m' nk')
                  | _ -> C.zero))
          | _ -> C.zero in
        let deeper : (a, m, n, b) C.t =
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
              | _ -> C.zero)
          | _ -> C.zero in
        C.add here deeper in
      C.add kills (strip n (fun c -> c))
  end

  (* Counting the 2-cells between two normal forms, cutting off at two, and constructing the cell if there is exactly one. *)
  type (_, _, _, _) count =
    | Zero_cells : ('a, 'm, 'n, 'b) count
    | One_cell : ('a, 'm, 'n, 'b) Modalcell.t -> ('a, 'm, 'n, 'b) count
    | Many_cells : ('a, 'm, 'n, 'b) count

  module Count = Enumerate (struct
    type ('a, 'm, 'n, 'b) t = ('a, 'm, 'n, 'b) count

    let zero = Zero_cells
    let one c = One_cell c

    let add : type a m n b. (a, m, n, b) t -> (a, m, n, b) t -> (a, m, n, b) t =
     fun x y ->
      match (x, y) with
      | Zero_cells, y -> y
      | x, Zero_cells -> x
      | _ -> Many_cells

    let map : type a m k b c p q d.
        ((a, m, k, b) Modalcell.t -> (c, p, q, d) Modalcell.t) -> (a, m, k, b) t -> (c, p, q, d) t =
     fun f -> function
      | Zero_cells -> Zero_cells
      | One_cell c -> One_cell (f c)
      | Many_cells -> Many_cells
  end)

  (* Listing all the 2-cells between two normal forms.  There are finitely many, since the recursion shortens one of the words at every step, and each is listed once. *)
  module All = Enumerate (struct
    type ('a, 'm, 'n, 'b) t = ('a, 'm, 'n, 'b) Modalcell.t list

    let zero = []
    let one c = [ c ]
    let add = ( @ )
    let map = List.map
  end)

  (* A 2-cell can be inserted as an implicit key only when it is unique; if there are several parallel cells, the user must disambiguate.  We normalize both modalities, count the cells between the normal forms, and compose with the normalization isomorphisms. *)
  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let (Normalize (_, xto, _)) = normalize x in
    let (Normalize (_, _, yfrom)) = normalize y in
    match Count.cells (Modalcell.vtgt xto) (Modalcell.vsrc yfrom) with
    | One_cell c -> Some (Modalcell.vcomp (Modalcell.vcomp yfrom c) xto)
    | Zero_cells | Many_cells -> None

  (* Since the normalizations are isomorphisms, composing with them is a bijection between the cells between two modalities and those between their normal forms, of which there are finitely many. *)
  let find_all : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t list option =
   fun x y ->
    let (Normalize (_, xto, _)) = normalize x in
    let (Normalize (_, _, yfrom)) = normalize y in
    Some
      (List.map
         (fun c -> Modalcell.vcomp (Modalcell.vcomp yfrom c) xto)
         (All.cells (Modalcell.vtgt xto) (Modalcell.vsrc yfrom)))

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

let install (module V : Variant) modes modalities modalcells =
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
  (* The renameable generators are the units and counits of the two adjunctions △⊣□ and ◇⊣∇; the iso inverses and the induced maps □⇒◇, △⇒∇ never need to be named. *)
  (match modalcells with
  | [] -> ()
  | [ tb_unit; tb_counit; dn_unit; dn_counit ] ->
      Modalcell.rename Cells.tb_unit tb_unit;
      Modalcell.rename Cells.tb_counit tb_counit;
      Modalcell.rename Cells.dn_unit dn_unit;
      Modalcell.rename Cells.dn_counit dn_counit
  | _ -> failwith "wrong number of modal cell names for gwpt mode theory");
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
