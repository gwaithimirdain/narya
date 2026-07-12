open Dim

(* A local geometric morphism has two modes, Disc(rete) and Type, and three generating modalities:

     △ : Disc → Type
     □ : Type → Disc
     ∇ : Disc → Type

   with an adjoint triple △ ⊣ □ ⊣ ∇, where the counit of □ ⊣ ∇ (namely □∇ ⇒ id_Disc) and the unit of △ ⊣ □ (namely id_Disc ⇒ □△) are isomorphisms.  The theory is locally posetal (any two parallel 2-cells are equal).

   Every composite modality is isomorphic to exactly one normal form: an identity, one of the three generators, or one of the composites △□ or ∇□ (both Type → Type).  This is because the only nontrivial reductions are the two isomorphisms □∇ ≅ id_Disc and □△ ≅ id_Disc, which cancel a □ immediately following (in application order) by a ∇ or a △.  The remaining nonidentity 2-cells between normal forms are the counit △□ ⇒ id, the unit id ⇒ ∇□, their composite △□ ⇒ ∇□, and an induced 2-cell △ ⇒ ∇ (either composite △ ≅ △□∇ ⇒ ∇ or △ ⇒ ∇□△ ≅ ∇). *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
  val nabla_tangible : bool
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "local"
  let nabla_tangible = true
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "local tconn"
  let nabla_tangible = false
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

module LocalCells
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen)
    (Triangle : Modality.Generated with module G := TriangleGen(V)(Disc)(Type))
    (Box : Modality.Generated with module G := BoxGen(V)(Disc)(Type))
    (Nabla : Modality.Generated with module G := NablaGen(V)(Disc)(Type)) =
struct
  let disc = Disc.mode
  let typ = Type.mode

  (* The three generating modalities. *)
  let tri = Modality.of_gen Triangle.modality
  let box = Modality.of_gen Box.modality
  let nab = Modality.of_gen Nabla.modality

  (* The two-generator composite modalities. *)
  let tribox = Modality.Path (Suc (Suc (Zero, Triangle.modality), Box.modality), typ)
  let boxtri = Modality.Path (Suc (Suc (Zero, Box.modality), Triangle.modality), disc)
  let nabbox = Modality.Path (Suc (Suc (Zero, Nabla.modality), Box.modality), typ)
  let boxnab = Modality.Path (Suc (Suc (Zero, Box.modality), Nabla.modality), disc)

  (* The generating 2-cells (source ⇒ target).  Both isomorphisms (◇△ ≅ id and □△ ≅ id) get an explicit inverse generator; since the theory is posetal, any parallel cell acts identically, so it does not matter that these are freely generated rather than literally inverse.
       box_counit : △□ ⇒ id_Type            nabla_unit : id_Type ⇒ △◇
       box_unit : id_Disc ⇒ □△ (iso)        box_unit_inv : □△ ⇒ id_Disc
       nabla_counit : ◇△ ⇒ id_Disc (iso)  nabla_counit_inv : id_Disc ⇒ ◇△
       box_to_dia : □ ⇒ ◇ *)
  let box_counit = Modalcell.of_gen (Modalcell.generate tribox (Modality.id typ))
  let nabla_unit = Modalcell.of_gen (Modalcell.generate (Modality.id typ) nabbox)
  let box_unit = Modalcell.of_gen (Modalcell.generate (Modality.id disc) boxtri)
  let box_unit_inv = Modalcell.of_gen (Modalcell.generate boxtri (Modality.id disc))
  let nabla_counit = Modalcell.of_gen (Modalcell.generate boxnab (Modality.id disc))
  let nabla_counit_inv = Modalcell.of_gen (Modalcell.generate (Modality.id disc) boxnab)
  let tri_to_nab = Modalcell.of_gen (Modalcell.generate tri nab)

  (* A modality is sinister (a declared left adjoint) if it is the identity, △ (left adjoint to □), or □ (left adjoint to ∇), or △□ (left adjoint to ∇□). *)
  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match
      ( Modality.compare_id f,
        Modality.compare f tri,
        Modality.compare f box,
        Modality.compare f tribox )
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
        (* □ ⊣ ∇ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = box;
                  right = nab;
                  right_left = Suc (Zero, Box.modality);
                  unit = nabla_unit;
                  left_right = Suc (Zero, Nabla.modality);
                  counit = nabla_counit;
                }))
    | _, _, _, Eq ->
        (* △□ ⊣ ∇□ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = tribox;
                  right = nabbox;
                  right_left = Suc (Suc (Zero, Triangle.modality), Box.modality);
                  unit =
                    Modalcell.vcomp
                      (Modalcell.prewhisker
                         (Suc (Zero, Box.modality))
                         (Suc (Zero, Box.modality))
                         (Modalcell.postwhisker Zero
                            (Suc (Suc (Zero, Box.modality), Triangle.modality))
                            nab box_unit)
                         box)
                      nabla_unit;
                  left_right = Suc (Suc (Zero, Nabla.modality), Box.modality);
                  counit =
                    Modalcell.vcomp box_counit
                      (Modalcell.prewhisker
                         (Suc (Zero, Box.modality))
                         (Suc (Zero, Box.modality))
                         (Modalcell.postwhisker
                            (Suc (Suc (Zero, Box.modality), Nabla.modality))
                            Zero tri nabla_counit)
                         box);
                }))
    | _ -> None

  (* Locally posetal: any two parallel 2-cells are equal. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  (* The unique 2-cell between two *normal-form* modalities, if one exists.  The nonidentity 2-cells between normal forms are exactly: the counit △□ ⇒ id, the unit id ⇒ ∇□, their composite △□ ⇒ ∇□, and the induced △ ⇒ ∇.  (Since the theory is posetal, any 2-cell of the correct source and target is "the" one.) *)
  let bridge : type a p q b.
      (a, p, b) Modality.t -> (a, q, b) Modality.t -> (a, p, q, b) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match
          ( Modality.compare m tribox,
            Modality.compare n (Modality.id typ),
            Modality.compare n nabbox,
            Modality.compare m (Modality.id typ),
            Modality.compare m tri,
            Modality.compare n nab )
        with
        | Eq, Eq, _, _, _, _ -> Some box_counit (* △□ ⇒ id *)
        | Eq, _, Eq, _, _, _ -> Some (Modalcell.vcomp nabla_unit box_counit) (* △□ ⇒ ∇□ *)
        | _, _, Eq, Eq, _, _ -> Some nabla_unit (* id ⇒ ∇□ *)
        | _, _, _, _, Eq, Eq -> Some tri_to_nab (* △ ⇒ ∇ *)
        | _ -> None)

  (* The normalization of a modality: an isomorphic normal form together with the isomorphism (in both directions).  Every modality is isomorphic to exactly one normal form. *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  (* Prepend a generator g (on the source side, i.e. applied first) to an already-normalized modality, and renormalize.  The only reductions are □∇ ≅ id and □△ ≅ id, which fire when g = ∇ or g = △ are prepended to a normal form beginning with □.  We are given the isomorphisms g_to : g·rest ⇒ g·nf and g_from : g·nf ⇒ g·rest obtained by prewhiskering the sub-isomorphisms by g, and we postcompose the reduction cell between g·nf and its normal form nf'. *)
  let prepend : type c gg a nf b gm.
      (c, gg, a) Modality.Gen.t ->
      (a, nf, b) Modality.t ->
      (c, gm, (nf, gg) Modality.suc, b) Modalcell.t ->
      (c, (nf, gg) Modality.suc, gm, b) Modalcell.t ->
      (c, gm, b) normalize =
   fun g nf g_to g_from ->
    match
      ( Modality.Gen.compare g Triangle.modality,
        Modality.Gen.compare g Nabla.modality,
        Modality.compare nf box,
        Modality.compare nf tribox,
        Modality.compare nf nabbox )
    with
    (* □△ ≅ id *)
    | Eq, _, Eq, _, _ ->
        Normalize
          (Modality.id disc, Modalcell.vcomp box_unit_inv g_to, Modalcell.vcomp g_from box_unit)
    (* □∇ ≅ id *)
    | _, Eq, Eq, _, _ ->
        Normalize
          ( Modality.id disc,
            Modalcell.vcomp nabla_counit g_to,
            Modalcell.vcomp g_from nabla_counit_inv )
    (* △□△ ≅ △ *)
    | Eq, _, _, Eq, _ ->
        Normalize
          ( tri,
            Modalcell.vcomp
              (Modalcell.postwhisker
                 (Suc (Suc (Zero, Box.modality), Triangle.modality))
                 Zero tri box_unit_inv)
              g_to,
            Modalcell.vcomp g_from
              (Modalcell.postwhisker Zero
                 (Suc (Suc (Zero, Box.modality), Triangle.modality))
                 tri box_unit) )
    (* ∇□△ ≅ ∇ *)
    | Eq, _, _, _, Eq ->
        Normalize
          ( nab,
            Modalcell.vcomp
              (Modalcell.postwhisker
                 (Suc (Suc (Zero, Box.modality), Triangle.modality))
                 Zero nab box_unit_inv)
              g_to,
            Modalcell.vcomp g_from
              (Modalcell.postwhisker Zero
                 (Suc (Suc (Zero, Box.modality), Triangle.modality))
                 nab box_unit) )
    (* △□∇ ≅ △ *)
    | _, Eq, _, Eq, _ ->
        Normalize
          ( tri,
            Modalcell.vcomp
              (Modalcell.postwhisker
                 (Suc (Suc (Zero, Box.modality), Nabla.modality))
                 Zero tri nabla_counit)
              g_to,
            Modalcell.vcomp g_from
              (Modalcell.postwhisker Zero
                 (Suc (Suc (Zero, Box.modality), Nabla.modality))
                 tri nabla_counit_inv) )
    (* ∇□∇ ≅ ∇ *)
    | _, Eq, _, _, Eq ->
        Normalize
          ( nab,
            Modalcell.vcomp
              (Modalcell.postwhisker
                 (Suc (Suc (Zero, Box.modality), Nabla.modality))
                 Zero nab nabla_counit)
              g_to,
            Modalcell.vcomp g_from
              (Modalcell.postwhisker Zero
                 (Suc (Suc (Zero, Box.modality), Nabla.modality))
                 nab nabla_counit_inv) )
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

  (* Every composite modality is isomorphic to a normal form (id, a generator, △□, or ∇□).  find_unique normalizes both modalities, looks up the bridge 2-cell between the normal forms, and composes with the isomorphisms. *)
  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let (Normalize (_, xto, _)) = normalize x in
    let (Normalize (_, _, yfrom)) = normalize y in
    match bridge (Modalcell.vtgt xto) (Modalcell.vsrc yfrom) with
    | Some b -> Some (Modalcell.vcomp (Modalcell.vcomp yfrom b) xto)
    | None -> None

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "cell_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))
end

module LocalModalities
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen)
    (Triangle : Modality.Generated with module G := TriangleGen(V)(Disc)(Type))
    (Box : Modality.Generated with module G := BoxGen(V)(Disc)(Type))
    (Nabla : Modality.Generated with module G := NablaGen(V)(Disc)(Type)) : Modality.Theory = struct
  open LocalCells (V) (Disc) (Type) (Triangle) (Box) (Nabla)

  let pellucid _ = false

  (* Every modality whose normalization doesn't contain a ∇ is transparent (that is, identities, □, △, and △□). *)
  let rec transparent_normal : type a m b. (a, m, b) Modality.t -> bool = function
    | Path (Zero, _) -> true
    | Path (Suc (m, g), mode) -> (
        match Modality.Gen.compare g Nabla.modality with
        | Eq -> false
        | Neq -> transparent_normal (Path (m, mode)))

  let transparent m =
    let (Normalize (m, _, _)) = normalize m in
    transparent_normal m

  (* In the discrete case, ∇ is not tangible or translucent, so that it doesn't become discrete (it should be codiscrete). *)
  let tangible : type a m b. (a, m, b) Modality.t -> bool =
   fun m ->
    match Modality.compare m nab with
    | Eq -> V.nabla_tangible
    | Neq -> true

  let translucent m = tangible m
end

let install (module V : Variant) modes modalities =
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
  let module Nabla = NablaGen (V) (Disc) (Type) in
  (match modalities with
  | [ tri; box; nabla ] ->
      Tri.name := tri;
      Box.name := box;
      Nabla.name := nabla
  | [] -> ()
  | _ -> failwith ("wrong number of modality names for " ^ V.name ^ " mode theory"));
  Modality.set_one_char true modalities;
  let module Triangle = Modality.Generate (Tri) in
  let module Box = Modality.Generate (Box) in
  let module Nabla = Modality.Generate (Nabla) in
  Modalcell.choose_theory
    (module LocalCells (V) (Disc) (Type) (Triangle) (Box) (Nabla) : Modalcell.Theory);
  Modality.choose_theory
    (module LocalModalities (V) (Disc) (Type) (Triangle) (Box) (Nabla) : Modality.Theory)
