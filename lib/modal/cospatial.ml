open Dim

(* A "cospatial" mode theory: one mode with two self-modality generators, a reflector ʃ
   (idempotent monad) and a coreflector ♭ (idempotent comonad), together with isomorphisms
   ʃ♭ ≅ ♭ and ♭ʃ ≅ ʃ.  These isomorphisms say that composing ʃ and ♭ in either order collapses
   to whichever generator was applied *first*: applying ♭ and then ʃ is the same as ♭ alone, and
   applying ʃ and then ♭ is the same as ʃ alone.  Consequently every composite word in ʃ and ♭
   reduces to its single, source-most generator (or to the identity, if the word is empty): there
   are only three normal forms, id, ʃ, and ♭, and no two of them are isomorphic.

   The theory is locally posetal (any two parallel 2-cells are declared equal), so we only need
   to decide *existence* of a 2-cell and exhibit *some* witness, not worry about coherence among
   different witnesses.  Combining the reflector's unit id ⇒ ʃ with the isomorphism ♭ʃ ≅ ʃ, and
   the coreflector's counit ♭ ⇒ id with the isomorphism ʃ♭ ≅ ♭, produces a unit id ⇒ ♭ʃ and a
   counit ʃ♭ ⇒ id, exhibiting an *induced* adjunction ʃ ⊣ ♭.  Since ʃ is thereby a declared left
   adjoint, it is sinister and (like the identity) transparent; ♭, the right adjoint, is
   neither. *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
  val locker : bool
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "cospatial"
  let locker = false
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete cospatial"
  let locker = true
end

module TypeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

(* In the discrete case, both modalities are discrete/nonparametric, since they land in the same subcategory. *)

module ShapeGen (V : Variant) (Type : Mode.Generated with module G := TypeGen) = struct
  type src = Type.t
  type tgt = Type.t

  let src = Type.mode
  let tgt = Type.mode
  let name = ref "ʃ"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module FlatGen (V : Variant) (Type : Mode.Generated with module G := TypeGen) = struct
  type src = Type.t
  type tgt = Type.t

  let src = Type.mode
  let tgt = Type.mode
  let name = ref "♭"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module CospatialCells
    (V : Variant)
    (Type : Mode.Generated with module G := TypeGen)
    (Shape : Modality.Generated with module G := ShapeGen(V)(Type))
    (Flat : Modality.Generated with module G := FlatGen(V)(Type)) =
struct
  let typ = Type.mode
  let shape = Modality.of_gen Shape.modality
  let flat = Modality.of_gen Flat.modality

  (* The two-generator composite modalities.  A modality Path (Suc (Suc (Zero, X), Y), tgt)
     applies Y first (source side) and then X, i.e. it is X ∘ Y.  So shapeshape = ʃ∘ʃ, flatflat =
     ♭∘♭, shapeflat = ʃ∘♭ (i.e. "ʃ♭", ♭ first), and flatshape = ♭∘ʃ (i.e. "♭ʃ", ʃ first). *)
  let shapeshape = Modality.Path (Suc (Suc (Zero, Shape.modality), Shape.modality), typ)
  let flatflat = Modality.Path (Suc (Suc (Zero, Flat.modality), Flat.modality), typ)
  let shapeflat = Modality.Path (Suc (Suc (Zero, Shape.modality), Flat.modality), typ)
  let flatshape = Modality.Path (Suc (Suc (Zero, Flat.modality), Shape.modality), typ)

  (* The generating 2-cells: the reflector's unit and multiplication, the coreflector's counit
     and comultiplication, and (both directions of) the two given isomorphisms.  As elsewhere,
     both isomorphisms get an explicit inverse generator; since the theory is posetal, it does
     not matter that these are freely generated rather than literally inverse. *)
  let shape_unit = Modalcell.of_gen (Modalcell.generate "ηʃ" (Modality.id typ) shape)
  let shape_mult = Modalcell.of_gen (Modalcell.generate "μʃ" shapeshape shape)
  let flat_counit = Modalcell.of_gen (Modalcell.generate "ε♭" flat (Modality.id typ))
  let flat_comult = Modalcell.of_gen (Modalcell.generate "Δ♭" flat flatflat)
  let sf_to = Modalcell.of_gen (Modalcell.generate "ʃ♭_to_♭" shapeflat flat) (* ʃ♭ ⇒ ♭ *)
  let sf_from = Modalcell.of_gen (Modalcell.generate "♭_to_ʃ♭" flat shapeflat) (* ♭ ⇒ ʃ♭ *)
  let fs_to = Modalcell.of_gen (Modalcell.generate "♭ʃ_to_ʃ" flatshape shape) (* ♭ʃ ⇒ ʃ *)
  let fs_from = Modalcell.of_gen (Modalcell.generate "ʃ_to_♭ʃ" shape flatshape) (* ʃ ⇒ ♭ʃ *)

  (* The "other halves" of the idempotence isomorphisms ʃʃ ≅ ʃ and ♭♭ ≅ ♭, obtained (as usual for
     an idempotent monad/comonad) by whiskering the unit/counit rather than as separate
     generators. *)
  let shape_mult_inv = Modalcell.postwhisker Zero (Suc (Zero, Shape.modality)) shape shape_unit
  let flat_comult_inv = Modalcell.postwhisker (Suc (Zero, Flat.modality)) Zero flat flat_counit

  (* The induced adjunction ʃ ⊣ ♭: unit id ⇒ ʃ ⇒ ♭ʃ and counit ʃ♭ ⇒ ♭ ⇒ id. *)
  let adj_unit = Modalcell.vcomp fs_from shape_unit
  let adj_counit = Modalcell.vcomp flat_counit sf_to

  (* A modality is sinister (a declared left adjoint) if it is the identity or ʃ (left adjoint to
     ♭); ♭, the right adjoint, is not itself sinister. *)
  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match (Modality.compare_id f, Modality.compare f shape) with
    | Eq, _ -> Some (Modalcell.id_sinister (Modality.src f))
    | _, Eq ->
        Some
          (Sinister
             (Adjunction
                {
                  left = shape;
                  right = flat;
                  right_left = Suc (Zero, Shape.modality);
                  unit = adj_unit;
                  left_right = Suc (Zero, Flat.modality);
                  counit = adj_counit;
                }))
    | _ -> None

  (* Locally posetal: any two parallel 2-cells are equal. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  (* The unique 2-cell between two *normal-form* modalities (id, ʃ, or ♭), if one exists: the
     unit id ⇒ ʃ, the counit ♭ ⇒ id, and their composite ♭ ⇒ ʃ.  There is no cell id ⇒ ♭ or ʃ ⇒ id
     or ʃ ⇒ ♭. *)
  let bridge : type a p q b.
      (a, p, b) Modality.t -> (a, q, b) Modality.t -> (a, p, q, b) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match Modality.compare m (Modality.id typ) with
        | Eq -> (
            match Modality.compare n shape with
            | Eq -> Some shape_unit (* id ⇒ ʃ *)
            | Neq -> None)
        | Neq -> (
            match Modality.compare m flat with
            | Eq -> (
                match Modality.compare n (Modality.id typ) with
                | Eq -> Some flat_counit (* ♭ ⇒ id *)
                | Neq -> (
                    match Modality.compare n shape with
                    | Eq -> Some (Modalcell.vcomp shape_unit flat_counit) (* ♭ ⇒ id ⇒ ʃ *)
                    | Neq -> None))
            | Neq -> None))

  (* The normalization of a modality: an isomorphic normal form together with the isomorphism (in
     both directions).  Every modality is isomorphic to exactly one of id, ʃ, ♭. *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  (* Prepend a generator g (on the source side, i.e. applied first) to an already-normalized
     modality, and renormalize.  Whatever nf is (id, ʃ, or ♭), the result always collapses to g
     alone: id absorbs trivially, a repeated generator collapses by idempotence, and a mixed pair
     collapses by one of the two given isomorphisms (with the newly-prepended, more source-side
     generator always the survivor).  We are given the isomorphisms g·rest ⇒ g·nf (g_to) and
     g·nf ⇒ g·rest (g_from) obtained by prewhiskering the sub-isomorphisms by g, and we postcompose
     the reduction cell between g·nf and its normal form g. *)
  let prepend : type c gg a nf b gm.
      (c, gg, a) Modality.Gen.t ->
      (a, nf, b) Modality.t ->
      (c, gm, (nf, gg) Modality.suc, b) Modalcell.t ->
      (c, (nf, gg) Modality.suc, gm, b) Modalcell.t ->
      (c, gm, b) normalize =
   fun g nf g_to g_from ->
    match
      ( Modality.Gen.compare g Shape.modality,
        Modality.Gen.compare g Flat.modality,
        Modality.compare nf (Modality.id typ),
        Modality.compare nf shape,
        Modality.compare nf flat )
    with
    (* g = ʃ *)
    | Eq, _, Eq, _, _ -> Normalize (shape, g_to, g_from) (* ʃ·id = ʃ *)
    | Eq, _, _, Eq, _ ->
        (* ʃ·ʃ = ʃʃ ≅ ʃ *)
        Normalize (shape, Modalcell.vcomp shape_mult g_to, Modalcell.vcomp g_from shape_mult_inv)
    | Eq, _, _, _, Eq ->
        (* ʃ·♭ = ♭ʃ ≅ ʃ *)
        Normalize (shape, Modalcell.vcomp fs_to g_to, Modalcell.vcomp g_from fs_from)
    (* g = ♭ *)
    | _, Eq, Eq, _, _ -> Normalize (flat, g_to, g_from) (* ♭·id = ♭ *)
    | _, Eq, _, Eq, _ ->
        (* ♭·ʃ = ʃ♭ ≅ ♭ *)
        Normalize (flat, Modalcell.vcomp sf_to g_to, Modalcell.vcomp g_from sf_from)
    | _, Eq, _, _, Eq ->
        (* ♭·♭ = ♭♭ ≅ ♭ *)
        Normalize (flat, Modalcell.vcomp flat_comult_inv g_to, Modalcell.vcomp g_from flat_comult)
    | _ -> failwith "cospatial: ill-typed or unrecognized modality composite in normalize"

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

  (* Every composite modality is isomorphic to a normal form (id, ʃ, or ♭).  find_unique
     normalizes both modalities, looks up the bridge 2-cell between the normal forms, and
     composes with the isomorphisms. *)
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
      | Eq -> Ok (Modalcell.Locker (flat, flat_counit))
      | Neq -> Ok (Locker (Modality.id m, Id (Modality.id m)))
    else Error "cospatial"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "cell_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))

  (* The theory of modality properties is nested inside the cells module, so that installing both
     theories instantiates this functor -- and in particular Modalcell.generate, which allocates
     fresh generating 2-cells -- only once. *)
  module Modalities : Modality.Theory = struct
    let tangible _ = true
    let pellucid _ = false

    (* The left adjoints (the identity and ʃ) are transparent; ♭ is not. *)
    let transparent : type a m b. (a, m, b) Modality.t -> bool =
     fun m ->
      let (Normalize (nf, _, _)) = normalize m in
      match Modality.compare nf flat with
      | Eq -> false
      | Neq -> true

    let translucent _ = true
  end
end

let install (module V : Variant) modes modalities =
  (match modes with
  | [ ty ] -> TypeGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for cospatial mode theory");
  let module Type = Mode.Generate (TypeGen) in
  let module Sh = ShapeGen (V) (Type) in
  let module Fl = FlatGen (V) (Type) in
  (match modalities with
  | [ shape; flat ] ->
      Sh.name := shape;
      Fl.name := flat
  | [] -> ()
  | _ -> failwith "wrong number of modality names for cospatial mode theory");
  Modality.set_one_char true modalities;
  let module Shape = Modality.Generate (Sh) in
  let module Flat = Modality.Generate (Fl) in
  let module Cells = CospatialCells (V) (Type) (Shape) (Flat) in
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
