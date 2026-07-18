open Dim

(* A totally connected geometric morphism has two modes, Disc(rete) and Type, and three generating modalities:

     △ : Disc → Type
     □ : Type → Disc
     ◇ : Type → Disc

   with an adjoint triple ◇ ⊣ △ ⊣ □, where the counit of ◇ ⊣ △ (namely ◇△ ⇒ id_Disc) and the unit of △ ⊣ □ (namely id_Disc ⇒ □△) are isomorphisms.  The theory is locally posetal (any two parallel 2-cells are equal).

   Every composite modality is isomorphic to exactly one normal form: an identity, one of the three generators, or one of the composites △□ or △◇ (both Type → Type).  This is because the only nontrivial reductions are the two isomorphisms ◇△ ≅ id_Disc and □△ ≅ id_Disc, which cancel a △ immediately followed (in application order) by a ◇ or a □.  The remaining nonidentity 2-cells between normal forms are the counit △□ ⇒ id, the unit id ⇒ △◇, their composite △□ ⇒ △◇, and an induced 2-cell □ ⇒ ◇. *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
  val locker : bool
  val dia_pellucid : bool
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "tconn"
  let locker = false
  let dia_pellucid = false
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete tconn"
  let locker = true
  let dia_pellucid = true
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

module TconnCells
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen)
    (Triangle : Modality.Generated with module G := TriangleGen(V)(Disc)(Type))
    (Box : Modality.Generated with module G := BoxGen(V)(Disc)(Type))
    (Diamond : Modality.Generated with module G := DiamondGen(V)(Disc)(Type)) =
struct
  let disc = Disc.mode
  let typ = Type.mode

  (* The three generating modalities. *)
  let tri = Modality.of_gen Triangle.modality
  let box = Modality.of_gen Box.modality
  let dia = Modality.of_gen Diamond.modality

  (* The two-generator composite modalities.  A modality Path (Suc (Suc (Zero, X), Y), tgt) applies Y first (source side) and then X, i.e. it is X ∘ Y.  So: tribox = △∘□ (Type→Type), tridia = △∘◇ (Type→Type), boxtri = □∘△ (Disc→Disc), diatri = ◇∘△ (Disc→Disc). *)
  let tribox = Modality.Path (Suc (Suc (Zero, Triangle.modality), Box.modality), typ)
  let tridia = Modality.Path (Suc (Suc (Zero, Triangle.modality), Diamond.modality), typ)
  let boxtri = Modality.Path (Suc (Suc (Zero, Box.modality), Triangle.modality), disc)
  let diatri = Modality.Path (Suc (Suc (Zero, Diamond.modality), Triangle.modality), disc)

  (* The generating 2-cells (source ⇒ target).  Both isomorphisms (◇△ ≅ id and □△ ≅ id) get an explicit inverse generator; since the theory is posetal, any parallel cell acts identically, so it does not matter that these are freely generated rather than literally inverse.
       box_counit : △□ ⇒ id_Type            diamond_unit : id_Type ⇒ △◇
       box_unit : id_Disc ⇒ □△ (iso)        box_unit_inv : □△ ⇒ id_Disc
       diamond_counit : ◇△ ⇒ id_Disc (iso)  diamond_counit_inv : id_Disc ⇒ ◇△
       box_to_dia : □ ⇒ ◇ *)
  let box_counit = Modalcell.of_gen (Modalcell.generate "ε△□" tribox (Modality.id typ))
  let diamond_unit = Modalcell.of_gen (Modalcell.generate "η△◇" (Modality.id typ) tridia)
  let box_unit = Modalcell.of_gen (Modalcell.generate "η□△" (Modality.id disc) boxtri)
  let box_unit_inv = Modalcell.of_gen (Modalcell.generate "η□△⁻¹" boxtri (Modality.id disc))
  let diamond_counit = Modalcell.of_gen (Modalcell.generate "ε◇△" diatri (Modality.id disc))

  let diamond_counit_inv = Modalcell.of_gen (Modalcell.generate "ε◇△⁻¹" (Modality.id disc) diatri)

  let box_to_dia = Modalcell.of_gen (Modalcell.generate "□_to_◇" box dia)

  (* A modality is sinister (a declared left adjoint) if it is the identity, △ (left adjoint to □), or ◇ (left adjoint to △), or △◇ (left adjoint to △□). *)
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
                  unit = box_unit;
                  left_right = Suc (Zero, Box.modality);
                  counit = box_counit;
                }))
    | _, _, Eq, _ ->
        (* ◇ ⊣ △ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = dia;
                  right = tri;
                  right_left = Suc (Zero, Diamond.modality);
                  unit = diamond_unit;
                  left_right = Suc (Zero, Triangle.modality);
                  counit = diamond_counit;
                }))
    | _, _, _, Eq ->
        (* △◇ ⊣ △□ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = tridia;
                  right = tribox;
                  right_left = Suc (Suc (Zero, Triangle.modality), Diamond.modality);
                  unit =
                    Modalcell.vcomp
                      (Modalcell.prewhisker
                         (Suc (Zero, Diamond.modality))
                         (Suc (Zero, Diamond.modality))
                         (Modalcell.postwhisker Zero
                            (Suc (Suc (Zero, Box.modality), Triangle.modality))
                            tri box_unit)
                         dia)
                      diamond_unit;
                  left_right = Suc (Suc (Zero, Triangle.modality), Box.modality);
                  counit =
                    Modalcell.vcomp box_counit
                      (Modalcell.prewhisker
                         (Suc (Zero, Box.modality))
                         (Suc (Zero, Box.modality))
                         (Modalcell.postwhisker
                            (Suc (Suc (Zero, Diamond.modality), Triangle.modality))
                            Zero tri diamond_counit)
                         box);
                }))
    | _ -> None

  (* Locally posetal: any two parallel 2-cells are equal. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  (* The unique 2-cell between two *normal-form* modalities, if one exists.  The nonidentity 2-cells between normal forms are exactly: the counit △□ ⇒ id, the unit id ⇒ △◇, their composite △□ ⇒ △◇, and the induced □ ⇒ ◇.  (Since the theory is posetal, any 2-cell of the correct source and target is "the" one.) *)
  let bridge : type a p q b.
      (a, p, b) Modality.t -> (a, q, b) Modality.t -> (a, p, q, b) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match
          ( Modality.compare m tribox,
            Modality.compare n (Modality.id typ),
            Modality.compare n tridia,
            Modality.compare m (Modality.id typ),
            Modality.compare m box,
            Modality.compare n dia )
        with
        | Eq, Eq, _, _, _, _ -> Some box_counit (* △□ ⇒ id *)
        | Eq, _, Eq, _, _, _ -> Some (Modalcell.vcomp diamond_unit box_counit) (* △□ ⇒ △◇ *)
        | _, _, Eq, Eq, _, _ -> Some diamond_unit (* id ⇒ △◇ *)
        | _, _, _, _, Eq, Eq -> Some box_to_dia (* □ ⇒ ◇ *)
        | _ -> None)

  (* The normalization of a modality: an isomorphic normal form together with the isomorphism (in both directions).  Every modality is isomorphic to exactly one normal form. *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  (* Prepend a generator g (on the source side, i.e. applied first) to an already-normalized modality, and renormalize.  The only reductions are ◇△ ≅ id and □△ ≅ id, which fire when g = △ is prepended to a normal form beginning with ◇ or □.  We are given the isomorphisms g·rest ⇒ g·nf (g_to) and g·nf ⇒ g·rest (g_from) obtained by prewhiskering the sub-isomorphisms by g, and we postcompose the reduction cell between g·nf and its normal form nf'. *)
  let prepend : type c gg a nf b gm.
      (c, gg, a) Modality.Gen.t ->
      (a, nf, b) Modality.t ->
      (c, gm, (nf, gg) Modality.suc, b) Modalcell.t ->
      (c, (nf, gg) Modality.suc, gm, b) Modalcell.t ->
      (c, gm, b) normalize =
   fun g nf g_to g_from ->
    match
      ( Modality.Gen.compare g Triangle.modality,
        Modality.Gen.compare g Box.modality,
        Modality.Gen.compare g Diamond.modality,
        Modality.compare nf (Modality.id typ),
        Modality.compare nf box,
        Modality.compare nf dia,
        Modality.compare nf (Modality.id disc),
        Modality.compare nf tri,
        Modality.compare nf tribox,
        Modality.compare nf tridia )
    with
    (* g = △ *)
    | Eq, _, _, Eq, _, _, _, _, _, _ -> Normalize (tri, g_to, g_from) (* △·id = △ *)
    | Eq, _, _, _, Eq, _, _, _, _, _ ->
        (* △·□ = □△ ≅ id_Disc *)
        Normalize
          (Modality.id disc, Modalcell.vcomp box_unit_inv g_to, Modalcell.vcomp g_from box_unit)
    | Eq, _, _, _, _, Eq, _, _, _, _ ->
        (* △·◇ = ◇△ ≅ id_Disc *)
        Normalize
          ( Modality.id disc,
            Modalcell.vcomp diamond_counit g_to,
            Modalcell.vcomp g_from diamond_counit_inv )
    | Eq, _, _, _, _, _, _, _, Eq, _ ->
        (* △·△□ = △∘□△ ≅ △ *)
        let tc =
          Modalcell.postwhisker
            (Suc (Suc (Zero, Box.modality), Triangle.modality))
            Zero tri box_unit_inv in
        let tcr =
          Modalcell.postwhisker Zero
            (Suc (Suc (Zero, Box.modality), Triangle.modality))
            tri box_unit in
        Normalize (tri, Modalcell.vcomp tc g_to, Modalcell.vcomp g_from tcr)
    | Eq, _, _, _, _, _, _, _, _, Eq ->
        (* △·△◇ = △∘◇△ ≅ △ *)
        let tc =
          Modalcell.postwhisker
            (Suc (Suc (Zero, Diamond.modality), Triangle.modality))
            Zero tri diamond_counit in
        let tcr =
          Modalcell.postwhisker Zero
            (Suc (Suc (Zero, Diamond.modality), Triangle.modality))
            tri diamond_counit_inv in
        Normalize (tri, Modalcell.vcomp tc g_to, Modalcell.vcomp g_from tcr)
    (* g = □ *)
    | _, Eq, _, _, _, _, Eq, _, _, _ -> Normalize (box, g_to, g_from) (* □·id = □ *)
    | _, Eq, _, _, _, _, _, Eq, _, _ -> Normalize (tribox, g_to, g_from) (* □·△ = △□ *)
    (* g = ◇ *)
    | _, _, Eq, _, _, _, Eq, _, _, _ -> Normalize (dia, g_to, g_from) (* ◇·id = ◇ *)
    | _, _, Eq, _, _, _, _, Eq, _, _ -> Normalize (tridia, g_to, g_from) (* ◇·△ = △◇ *)
    | _ -> failwith "dtt: ill-typed or unrecognized modality composite in normalize"

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

  (* Every composite modality is isomorphic to a normal form (id, a generator, △□, or △◇).  find_unique normalizes both modalities, looks up the bridge 2-cell between the normal forms, and composes with the isomorphisms. *)
  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let (Normalize (_, xto, _)) = normalize x in
    let (Normalize (_, _, yfrom)) = normalize y in
    match bridge (Modalcell.vtgt xto) (Modalcell.vsrc yfrom) with
    | Some b -> Some (Modalcell.vcomp (Modalcell.vcomp yfrom b) xto)
    | None -> None

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun m ->
    if V.locker then
      match Mode.compare m Type.mode with
      | Eq -> Ok (Modalcell.Locker (tribox, box_counit))
      | Neq -> Ok (Locker (Modality.id m, Id (Modality.id m)))
    else Error "tconn"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "cell_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))

  (* The theory of modality properties is nested inside the cells module, so that installing both theories instantiates this functor -- and in particular Modalcell.generate, which allocates fresh generating 2-cells -- only once. *)
  module Modalities : Modality.Theory = struct
    let tangible _ = true

    (* All left adjoints are transparent (△, ◇, and △◇). *)
    let rec transparent_normal : type a m b. (a, m, b) Modality.t -> bool = function
      | Path (Zero, _) -> true
      | Path (Suc (m, g), mode) -> (
          match Modality.Gen.compare g Box.modality with
          | Eq -> false
          | Neq -> transparent_normal (Path (m, mode)))

    let transparent m =
      let (Normalize (m, _, _)) = normalize m in
      transparent_normal m

    (* △ is always pellucid since it is the inverse image of a locally connected geometric morphism.  Additionally, in the discrete and external case, where we have a specific semantics in mind in *(EI-)inverse* diagrams with ◇ being evaluation at 0, it is also pellucid. *)
    let pellucid : type a m b. (a, m, b) Modality.t -> bool =
     fun m ->
      if (not V.dia_pellucid) && Endpoints.internal () then
        match Modality.compare m tri with
        | Eq -> true
        | Neq -> false
      else transparent m

    let translucent _ = true
  end
end

let install (module V : Variant) modes modalities modalcells =
  (match modalcells with
  | [] -> ()
  | _ -> failwith ("wrong number of modal cell names for " ^ V.name ^ " mode theory"));
  let module Disc = DiscGen (V) in
  (match modes with
  | [ disc; ty ] ->
      Disc.name := disc;
      TypeGen.name := ty
  | [] -> ()
  | _ -> failwith ("wrong number of mode names for " ^ V.name ^ " mode theory"));
  let module Disc = Mode.Generate (Disc) in
  let module Type = Mode.Generate (TypeGen) in
  let module Tri = TriangleGen (V) (Disc) (Type) in
  let module Box = BoxGen (V) (Disc) (Type) in
  let module Dia = DiamondGen (V) (Disc) (Type) in
  (match modalities with
  | [ dia; tri; box ] ->
      Dia.name := dia;
      Tri.name := tri;
      Box.name := box
  | [] -> ()
  | _ -> failwith ("wrong number of modality names for " ^ V.name ^ " mode theory"));
  Modality.set_one_char true modalities;
  let module Triangle = Modality.Generate (Tri) in
  let module Box = Modality.Generate (Box) in
  let module Diamond = Modality.Generate (Dia) in
  let module Cells = TconnCells (V) (Disc) (Type) (Triangle) (Box) (Diamond) in
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
