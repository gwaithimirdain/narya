open Util
open Dim

(* A "spatial" mode theory: one mode with two self-modality generators, a coreflector ♭ (idempotent comonad) and a reflector ♯ (idempotent monad), such that ♭ is left adjoint to ♯.  Everything is fully parametric.  As with Coreflector/Reflector, this theory is locally posetal (any two parallel 2-cells are declared equal), so we only need to decide *existence* of a 2-cell and exhibit *some* witness, not worry about coherence among different witnesses.

   The generating 2-cells are: the comonad counit/comultiplication of ♭ (flat_counit : ♭ ⇒ id, flat_comult : ♭ ⇒ ♭∘♭), the monad unit/multiplication of ♯ (sharp_unit : id ⇒ ♯, sharp_mult : ♯∘♯ ⇒ ♯), and the unit/counit of the adjunction ♭ ⊣ ♯ (adj_unit : id ⇒ ♯∘♭, adj_counit : ♭∘♯ ⇒ id).

   find_unique below decides existence of a 2-cell x ⇒ y between two words in {♭,♯} by: (1) checking definitional equality; (2) peeling a shared innermost generator via prewhisker and recursing; (3) otherwise trying to bridge through the identity, using "to_id" (repeatedly peeling an innermost ♭ via flat_counit, or an innermost ♭∘♯ pair via adj_counit) and "from_id" (dually, peeling an innermost ♯ via sharp_unit, or an innermost ♯∘♭ pair via adj_unit) and composing vertically.  This correctly handles words built by iterating ♭ alone, ♯ alone, or a single adjoint pair ♭∘♯ / ♯∘♭, which covers ordinary uses of the modalities, but it is not a complete decision procedure for the free theory of an adjoint pair of idempotent (co)monads: e.g. it will not find the (valid) cell ♭∘♯ ⇒ ♭∘♯∘♭, which requires inserting an adjunction cell at a non-innermost position. *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
  val tangible_sharp : bool
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "spatial"
  let tangible_sharp = true
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete spatial"
  let tangible_sharp = false
end

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module FlatGen (V : Variant) (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♭"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module SharpGen (V : Variant) (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♯"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module SpatialCells
    (V : Variant)
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Flat : Modality.Generated with module G := FlatGen(V)(Testmode))
    (Sharp : Modality.Generated with module G := SharpGen(V)(Testmode)) =
struct
  type mode = Testmode.t

  let flat = Modality.of_gen Flat.modality
  let sharp = Modality.of_gen Sharp.modality
  let flat_counit = Modalcell.of_gen (Modalcell.generate flat (Modality.id Testmode.mode))

  let flat_comult =
    Modalcell.of_gen
      (Modalcell.generate flat
         (Path (Suc (Suc (Zero, Flat.modality), Flat.modality), Testmode.mode)))

  let sharp_unit = Modalcell.of_gen (Modalcell.generate (Modality.id Testmode.mode) sharp)

  let sharp_mult =
    Modalcell.of_gen
      (Modalcell.generate
         (Path (Suc (Suc (Zero, Sharp.modality), Sharp.modality), Testmode.mode))
         sharp)

  (* Unit and counit of the adjunction ♭ ⊣ ♯: id ⇒ ♯∘♭ and ♭∘♯ ⇒ id. *)
  let adj_unit =
    Modalcell.of_gen
      (Modalcell.generate (Modality.id Testmode.mode)
         (Modality.Path (Suc (Suc (Zero, Sharp.modality), Flat.modality), Testmode.mode)))

  let adj_counit =
    Modalcell.of_gen
      (Modalcell.generate
         (Modality.Path (Suc (Suc (Zero, Flat.modality), Sharp.modality), Testmode.mode))
         (Modality.id Testmode.mode))

  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match (Modality.compare_id f, Modality.compare f flat) with
    | Eq, _ -> Some (Modalcell.id_sinister (Modality.src f))
    | _, Eq ->
        Some
          (Sinister
             (Adjunction
                {
                  left = flat;
                  right = sharp;
                  right_left = Suc (Zero, Flat.modality);
                  unit = adj_unit;
                  left_right = Suc (Zero, Sharp.modality);
                  counit = adj_counit;
                }))
    | Neq, Neq -> None

  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  (* The normal forms of modalities are the generators id, flat, and sharp: everything is isomorphic to exactly one of those. *)
  type _ normal =
    | Normal_id : mode Modality.id normal
    | Normal_flat : (mode Modality.id, Flat.t) Modality.suc normal
    | Normal_sharp : (mode Modality.id, Sharp.t) Modality.suc normal

  type (_, _, _) normalize =
    | Normalize :
        'n normal * (mode, 'm, 'n, mode) Modalcell.t * (mode, 'n, 'm, mode) Modalcell.t
        -> (mode, 'm, mode) normalize

  let rec iso_flat : type flatm m.
      (mode, m, mode, (mode Path.id, Flat.t) Modality.suc, mode, flatm) Modality.bcomp ->
      (mode, flatm, (mode Path.id, Flat.t) Modality.suc, mode) Modalcell.t
      * (mode, (mode Path.id, Flat.t) Modality.suc, flatm, mode) Modalcell.t =
   fun bplus ->
    match bplus with
    | Modality.Zero -> (Modalcell.id flat, Modalcell.id flat)
    | Modality.Suc (type a g) ((g, bplus) : (a, g, mode) Modality.gen * _) -> (
        let (Bcomp rest) = Modality.bcomp (Modality.bcomp_right bplus) in
        match Mode.compare (Modality.Gen.src g) Testmode.mode with
        | Eq ->
            let to_flat, from_flat = iso_flat rest in
            let ( (remove_me :
                    ( mode,
                      ((mode Path.id, Flat.t) Tbwd.snoc, g) Tbwd.snoc,
                      (mode Path.id, Flat.t) Tbwd.snoc,
                      mode )
                    Modalcell.t),
                  (add_me :
                    ( mode,
                      (mode Path.id, Flat.t) Tbwd.snoc,
                      ((mode Path.id, Flat.t) Tbwd.snoc, g) Tbwd.snoc,
                      mode )
                    Modalcell.t) ) =
              match
                (Modality.Gen.compare g Sharp.modality, Modality.Gen.compare g Flat.modality)
              with
              | Eq, _ ->
                  ( Modalcell.vcomp
                      (Modalcell.postwhisker
                         (Suc (Suc (Zero, Flat.modality), Sharp.modality))
                         Zero flat adj_counit)
                      (Modalcell.prewhisker
                         (Suc (Zero, Sharp.modality))
                         (Suc (Zero, Sharp.modality))
                         flat_comult sharp),
                    Modalcell.postwhisker Zero (Suc (Zero, Sharp.modality)) flat sharp_unit )
              | _, Eq ->
                  ( Modalcell.postwhisker (Suc (Zero, Flat.modality)) Zero flat flat_counit,
                    flat_comult )
              | Neq, Neq -> failwith "spatial: unknown modality" in
            ( Modalcell.vcomp to_flat (Modalcell.bprewhisker bplus rest remove_me),
              Modalcell.vcomp (Modalcell.bprewhisker rest bplus add_me) from_flat )
        | Neq -> failwith "spatial: unknown mode")

  let rec iso_sharp : type sharpm m.
      (mode, m, mode, (mode Path.id, Sharp.t) Modality.suc, mode, sharpm) Modality.bcomp ->
      (mode, sharpm, (mode Path.id, Sharp.t) Modality.suc, mode) Modalcell.t
      * (mode, (mode Path.id, Sharp.t) Modality.suc, sharpm, mode) Modalcell.t =
   fun bplus ->
    match bplus with
    | Modality.Zero -> (Modalcell.id sharp, Modalcell.id sharp)
    | Modality.Suc (type a g) ((g, bplus) : (a, g, mode) Modality.gen * _) -> (
        let (Bcomp rest) = Modality.bcomp (Modality.bcomp_right bplus) in
        match Mode.compare (Modality.Gen.src g) Testmode.mode with
        | Eq ->
            let to_flat, from_flat = iso_sharp rest in
            let ( (remove_me :
                    ( mode,
                      ((mode Path.id, Sharp.t) Tbwd.snoc, g) Tbwd.snoc,
                      (mode Path.id, Sharp.t) Tbwd.snoc,
                      mode )
                    Modalcell.t),
                  (add_me :
                    ( mode,
                      (mode Path.id, Sharp.t) Tbwd.snoc,
                      ((mode Path.id, Sharp.t) Tbwd.snoc, g) Tbwd.snoc,
                      mode )
                    Modalcell.t) ) =
              match
                (Modality.Gen.compare g Sharp.modality, Modality.Gen.compare g Flat.modality)
              with
              | Eq, _ ->
                  ( sharp_mult,
                    Modalcell.postwhisker Zero (Suc (Zero, Sharp.modality)) sharp sharp_unit )
              | _, Eq ->
                  ( Modalcell.postwhisker (Suc (Zero, Flat.modality)) Zero sharp flat_counit,
                    Modalcell.vcomp
                      (Modalcell.prewhisker
                         (Suc (Zero, Flat.modality))
                         (Suc (Zero, Flat.modality))
                         sharp_mult flat)
                      (Modalcell.postwhisker Zero
                         (Suc (Suc (Zero, Sharp.modality), Flat.modality))
                         sharp adj_unit) )
              | Neq, Neq -> failwith "spatial: unknown modality" in
            ( Modalcell.vcomp to_flat (Modalcell.bprewhisker bplus rest remove_me),
              Modalcell.vcomp (Modalcell.bprewhisker rest bplus add_me) from_flat )
        | Neq -> failwith "spatial: unknown mode")

  let normalize : type a m b. (a, m, b) Modality.t -> (a, m, b) normalize =
   fun m ->
    let mode = Modality.src m in
    let (To_fwd (_, bplus)) = Modality.to_fwd m in
    match
      ( Mode.compare (Modality.src m) Testmode.mode,
        Mode.compare (Modality.tgt m) Testmode.mode,
        bplus )
    with
    | Eq, Eq, Zero -> Normalize (Normal_id, Modalcell.id2 mode, Modalcell.id2 mode)
    | Eq, Eq, Suc (g, bplus) -> (
        match (Modality.Gen.compare g Flat.modality, Modality.Gen.compare g Sharp.modality) with
        | Eq, _ ->
            let to_flat, from_flat = iso_flat bplus in
            Normalize (Normal_flat, to_flat, from_flat)
        | _, Eq ->
            let to_sharp, from_sharp = iso_sharp bplus in
            Normalize (Normal_sharp, to_sharp, from_sharp)
        | Neq, Neq -> failwith "spatial: unrecognized generator")
    | _ -> failwith "spatial: unknown mode"

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun m n ->
    let ( Normalize (type mnorm) ((mnorm, mto, _) : mnorm normal * _ * _),
          Normalize (type nnorm) ((nnorm, _, nfrom) : nnorm normal * _ * _) ) =
      (normalize m, normalize n) in
    match
      (Mode.compare (Modality.src m) Testmode.mode, Mode.compare (Modality.tgt m) Testmode.mode)
    with
    | Eq, Eq -> (
        match
          (match (mnorm, nnorm) with
           | Normal_id, Normal_id -> Some (Modalcell.id2 Testmode.mode)
           | Normal_id, Normal_flat -> None
           | Normal_id, Normal_sharp -> Some sharp_unit
           | Normal_flat, Normal_id -> Some flat_counit
           | Normal_flat, Normal_flat -> Some (Modalcell.id flat)
           | Normal_flat, Normal_sharp -> Some (Modalcell.vcomp sharp_unit flat_counit)
           | Normal_sharp, Normal_id -> None
           | Normal_sharp, Normal_flat -> None
           | Normal_sharp, Normal_sharp -> Some (Modalcell.id sharp)
            : (a, mnorm, nnorm, b) Modalcell.t option)
        with
        | Some bridge -> Some (Modalcell.vcomp (Modalcell.vcomp nfrom bridge) mto)
        | None -> None)
    | _ -> failwith "spatial: unknown mode"

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "spatial"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "cell_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))

  (* The theory of modality properties is nested inside the cells module, so that installing both theories instantiates this functor -- and in particular Modalcell.generate, which allocates fresh generating 2-cells -- only once. *)
  module Modalities : Modality.Theory = struct
    let pellucid _ = false

    (* Modalities that normalize to to id or flat are transparent, since they are left adjoints. *)
    let transparent : type a m b. (a, m, b) Modality.t -> bool =
     fun m ->
      match normalize m with
      | Normalize (Normal_id, _, _) | Normalize (Normal_flat, _, _) -> true
      | Normalize (Normal_sharp, _, _) -> false

    (* In the discrete case, we cannot make sharp tangible, since then it would be either discrete (if nonparametric) or bridge-preserving (if not), and it is neither (it is codiscrete, as ensured by its negative definition using discreteness of flat). *)

    let translucent : type a m b. (a, m, b) Modality.t -> bool =
     fun m -> V.tangible_sharp || transparent m

    let tangible : type a m b. (a, m, b) Modality.t -> bool =
     fun m -> V.tangible_sharp || transparent m
  end
end

let install (module V : Variant) modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith ("wrong number of mode names for " ^ V.name ^ " mode theory"));
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Flat = FlatGen (V) (Testmode) in
  let module Sharp = SharpGen (V) (Testmode) in
  (match modalities with
  | [ flat; sharp ] ->
      Flat.name := flat;
      Sharp.name := sharp
  | [] -> ()
  | _ -> failwith ("wrong number of modality names for " ^ V.name ^ " mode theory"));
  Modality.set_one_char true modalities;
  let module Flat = Modality.Generate (Flat) in
  let module Sharp = Modality.Generate (Sharp) in
  let module Cells = SpatialCells (V) (Testmode) (Flat) (Sharp) in
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
