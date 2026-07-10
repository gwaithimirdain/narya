open Util
open Dim

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module FlatGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♭"

  type nonparametric = D.one

  let nonparametric = D.one
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

module SpatialCells
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Flat : Modality.Generated with module G := FlatGen(Testmode))
    (Sharp : Modality.Generated with module G := SharpGen(Testmode)) =
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

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "cell_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))
end

(* Only modalities that normalize to to id or flat are tangible and translucent, and they are also transparent. *)
module SpatialModalities
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Flat : Modality.Generated with module G := FlatGen(Testmode))
    (Sharp : Modality.Generated with module G := SharpGen(Testmode)) : Modality.Theory = struct
  open SpatialCells (Testmode) (Flat) (Sharp)

  let pellucid _ = false

  let transparent : type a m b. (a, m, b) Modality.t -> bool =
   fun m ->
    match normalize m with
    | Normalize (Normal_id, _, _) | Normalize (Normal_flat, _, _) -> true
    | Normalize (Normal_sharp, _, _) -> false

  let translucent : type a m b. (a, m, b) Modality.t -> bool = fun m -> transparent m
  let tangible : type a m b. (a, m, b) Modality.t -> bool = fun m -> transparent m
  let parametric_locker : type a. a Mode.t -> (a, a) Modality.wrapped option = fun _ -> None
end

let install modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for discrete spatial mode theory");
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Flat = FlatGen (Testmode) in
  let module Sharp = SharpGen (Testmode) in
  (match modalities with
  | [ flat; sharp ] ->
      Flat.name := flat;
      Sharp.name := sharp
  | [] -> ()
  | _ -> failwith "wrong number of modality names for discrete spatial mode theory");
  Modality.set_one_char true modalities;
  let module Flat = Modality.Generate (Flat) in
  let module Sharp = Modality.Generate (Sharp) in
  Modalcell.choose_theory (module SpatialCells (Testmode) (Flat) (Sharp) : Modalcell.Theory);
  Modality.choose_theory (module SpatialModalities (Testmode) (Flat) (Sharp) : Modality.Theory)
