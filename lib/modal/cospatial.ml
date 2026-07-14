open Dim

(* A "cospatial" mode theory: one mode with two self-modality generators, a reflector ♯
   (idempotent monad) and a coreflector ♭ (idempotent comonad), together with isomorphisms
   ♯♭ ≅ ♭ and ♭♯ ≅ ♯.  These isomorphisms say that composing ♯ and ♭ in either order collapses
   to whichever generator was applied *first*: applying ♭ and then ♯ is the same as ♭ alone, and
   applying ♯ and then ♭ is the same as ♯ alone.  Consequently every composite word in ♯ and ♭
   reduces to its single, source-most generator (or to the identity, if the word is empty): there
   are only three normal forms, id, ♯, and ♭, and no two of them are isomorphic.

   The theory is locally posetal (any two parallel 2-cells are declared equal), so we only need
   to decide *existence* of a 2-cell and exhibit *some* witness, not worry about coherence among
   different witnesses.  Combining the reflector's unit id ⇒ ♯ with the isomorphism ♭♯ ≅ ♯, and
   the coreflector's counit ♭ ⇒ id with the isomorphism ♯♭ ≅ ♭, produces a unit id ⇒ ♭♯ and a
   counit ♯♭ ⇒ id, exhibiting an *induced* adjunction ♯ ⊣ ♭.  Since ♯ is thereby a declared left
   adjoint, it is sinister and (like the identity) transparent; ♭, the right adjoint, is
   neither. *)

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module SharpGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♯"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module FlatGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♭"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module CospatialCells
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Sharp : Modality.Generated with module G := SharpGen(Testmode))
    (Flat : Modality.Generated with module G := FlatGen(Testmode)) =
struct
  let typ = Testmode.mode
  let sharp = Modality.of_gen Sharp.modality
  let flat = Modality.of_gen Flat.modality

  (* The two-generator composite modalities.  A modality Path (Suc (Suc (Zero, X), Y), tgt)
     applies Y first (source side) and then X, i.e. it is X ∘ Y.  So sharpsharp = ♯∘♯, flatflat =
     ♭∘♭, sharpflat = ♯∘♭ (i.e. "♯♭", ♭ first), and flatsharp = ♭∘♯ (i.e. "♭♯", ♯ first). *)
  let sharpsharp = Modality.Path (Suc (Suc (Zero, Sharp.modality), Sharp.modality), typ)
  let flatflat = Modality.Path (Suc (Suc (Zero, Flat.modality), Flat.modality), typ)
  let sharpflat = Modality.Path (Suc (Suc (Zero, Sharp.modality), Flat.modality), typ)
  let flatsharp = Modality.Path (Suc (Suc (Zero, Flat.modality), Sharp.modality), typ)

  (* The generating 2-cells: the reflector's unit and multiplication, the coreflector's counit
     and comultiplication, and (both directions of) the two given isomorphisms.  As elsewhere,
     both isomorphisms get an explicit inverse generator; since the theory is posetal, it does
     not matter that these are freely generated rather than literally inverse. *)
  let sharp_unit = Modalcell.of_gen (Modalcell.generate (Modality.id typ) sharp)
  let sharp_mult = Modalcell.of_gen (Modalcell.generate sharpsharp sharp)
  let flat_counit = Modalcell.of_gen (Modalcell.generate flat (Modality.id typ))
  let flat_comult = Modalcell.of_gen (Modalcell.generate flat flatflat)
  let sf_to = Modalcell.of_gen (Modalcell.generate sharpflat flat) (* ♯♭ ⇒ ♭ *)
  let sf_from = Modalcell.of_gen (Modalcell.generate flat sharpflat) (* ♭ ⇒ ♯♭ *)
  let fs_to = Modalcell.of_gen (Modalcell.generate flatsharp sharp) (* ♭♯ ⇒ ♯ *)
  let fs_from = Modalcell.of_gen (Modalcell.generate sharp flatsharp) (* ♯ ⇒ ♭♯ *)

  (* The "other halves" of the idempotence isomorphisms ♯♯ ≅ ♯ and ♭♭ ≅ ♭, obtained (as usual for
     an idempotent monad/comonad) by whiskering the unit/counit rather than as separate
     generators. *)
  let sharp_mult_inv = Modalcell.postwhisker Zero (Suc (Zero, Sharp.modality)) sharp sharp_unit
  let flat_comult_inv = Modalcell.postwhisker (Suc (Zero, Flat.modality)) Zero flat flat_counit

  (* The induced adjunction ♯ ⊣ ♭: unit id ⇒ ♯ ⇒ ♭♯ and counit ♯♭ ⇒ ♭ ⇒ id. *)
  let adj_unit = Modalcell.vcomp fs_from sharp_unit
  let adj_counit = Modalcell.vcomp flat_counit sf_to

  (* A modality is sinister (a declared left adjoint) if it is the identity or ♯ (left adjoint to
     ♭); ♭, the right adjoint, is not itself sinister. *)
  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match (Modality.compare_id f, Modality.compare f sharp) with
    | Eq, _ -> Some (Modalcell.id_sinister (Modality.src f))
    | _, Eq ->
        Some
          (Sinister
             (Adjunction
                {
                  left = sharp;
                  right = flat;
                  right_left = Suc (Zero, Sharp.modality);
                  unit = adj_unit;
                  left_right = Suc (Zero, Flat.modality);
                  counit = adj_counit;
                }))
    | _ -> None

  (* Locally posetal: any two parallel 2-cells are equal. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  (* The unique 2-cell between two *normal-form* modalities (id, ♯, or ♭), if one exists: the
     unit id ⇒ ♯, the counit ♭ ⇒ id, and their composite ♭ ⇒ ♯.  There is no cell id ⇒ ♭ or ♯ ⇒ id
     or ♯ ⇒ ♭. *)
  let bridge : type a p q b.
      (a, p, b) Modality.t -> (a, q, b) Modality.t -> (a, p, q, b) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match Modality.compare m (Modality.id typ) with
        | Eq -> (
            match Modality.compare n sharp with
            | Eq -> Some sharp_unit (* id ⇒ ♯ *)
            | Neq -> None)
        | Neq -> (
            match Modality.compare m flat with
            | Eq -> (
                match Modality.compare n (Modality.id typ) with
                | Eq -> Some flat_counit (* ♭ ⇒ id *)
                | Neq -> (
                    match Modality.compare n sharp with
                    | Eq -> Some (Modalcell.vcomp sharp_unit flat_counit) (* ♭ ⇒ id ⇒ ♯ *)
                    | Neq -> None))
            | Neq -> None))

  (* The normalization of a modality: an isomorphic normal form together with the isomorphism (in
     both directions).  Every modality is isomorphic to exactly one of id, ♯, ♭. *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  (* Prepend a generator g (on the source side, i.e. applied first) to an already-normalized
     modality, and renormalize.  Whatever nf is (id, ♯, or ♭), the result always collapses to g
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
      ( Modality.Gen.compare g Sharp.modality,
        Modality.Gen.compare g Flat.modality,
        Modality.compare nf (Modality.id typ),
        Modality.compare nf sharp,
        Modality.compare nf flat )
    with
    (* g = ♯ *)
    | Eq, _, Eq, _, _ -> Normalize (sharp, g_to, g_from) (* ♯·id = ♯ *)
    | Eq, _, _, Eq, _ ->
        (* ♯·♯ = ♯♯ ≅ ♯ *)
        Normalize (sharp, Modalcell.vcomp sharp_mult g_to, Modalcell.vcomp g_from sharp_mult_inv)
    | Eq, _, _, _, Eq ->
        (* ♯·♭ = ♭♯ ≅ ♯ *)
        Normalize (sharp, Modalcell.vcomp fs_to g_to, Modalcell.vcomp g_from fs_from)
    (* g = ♭ *)
    | _, Eq, Eq, _, _ -> Normalize (flat, g_to, g_from) (* ♭·id = ♭ *)
    | _, Eq, _, Eq, _ ->
        (* ♭·♯ = ♯♭ ≅ ♭ *)
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

  (* Every composite modality is isomorphic to a normal form (id, ♯, or ♭).  find_unique
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
   fun _ -> Error "cospatial"

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

    (* The left adjoints (the identity and ♯) are transparent; ♭ is not. *)
    let transparent : type a m b. (a, m, b) Modality.t -> bool =
     fun m ->
      let (Normalize (nf, _, _)) = normalize m in
      match Modality.compare nf flat with
      | Eq -> false
      | Neq -> true

    let translucent _ = true
  end
end

let install modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for cospatial mode theory");
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Sh = SharpGen (Testmode) in
  let module Fl = FlatGen (Testmode) in
  (match modalities with
  | [ sharp; flat ] ->
      Sh.name := sharp;
      Fl.name := flat
  | [] -> ()
  | _ -> failwith "wrong number of modality names for cospatial mode theory");
  Modality.set_one_char true modalities;
  let module Sharp = Modality.Generate (Sh) in
  let module Flat = Modality.Generate (Fl) in
  let module Cells = CospatialCells (Testmode) (Sharp) (Flat) in
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
