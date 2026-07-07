(* A "spatial" mode theory: one mode with two self-modality generators, a coreflector ♭ (idempotent comonad) and a reflector ♯ (idempotent monad), such that ♭ is left adjoint to ♯.  Everything is fully parametric.  As with Coreflector/Reflector, this theory is locally posetal (any two parallel 2-cells are declared equal), so we only need to decide *existence* of a 2-cell and exhibit *some* witness, not worry about coherence among different witnesses.

   The generating 2-cells are: the comonad counit/comultiplication of ♭ (flat_counit : ♭ ⇒ id, flat_comult : ♭ ⇒ ♭∘♭), the monad unit/multiplication of ♯ (sharp_unit : id ⇒ ♯, sharp_mult : ♯∘♯ ⇒ ♯), and the unit/counit of the adjunction ♭ ⊣ ♯ (adj_unit : id ⇒ ♯∘♭, adj_counit : ♭∘♯ ⇒ id).

   find_unique below decides existence of a 2-cell x ⇒ y between two words in {♭,♯} by: (1) checking definitional equality; (2) peeling a shared innermost generator via prewhisker and recursing; (3) otherwise trying to bridge through the identity, using "to_id" (repeatedly peeling an innermost ♭ via flat_counit, or an innermost ♭∘♯ pair via adj_counit) and "from_id" (dually, peeling an innermost ♯ via sharp_unit, or an innermost ♯∘♭ pair via adj_unit) and composing vertically.  This correctly handles words built by iterating ♭ alone, ♯ alone, or a single adjoint pair ♭∘♯ / ♯∘♭, which covers ordinary uses of the modalities, but it is not a complete decision procedure for the free theory of an adjoint pair of idempotent (co)monads: e.g. it will not find the (valid) cell ♭∘♯ ⇒ ♭∘♯∘♭, which requires inserting an adjunction cell at a non-innermost position. *)

open Util
open Dim

module TestmodeGen = struct
  let name = "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module FlatGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = "♭"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module SharpGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = "♯"

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
    match Modality.compare f flat with
    | Eq ->
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
    | Neq -> None

  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  open Monad.Ops (Monad.Maybe)

  (* Repeatedly peel an innermost ♭ (via flat_counit) or an innermost ♭∘♯ pair (via adj_counit) to reach a cell x ⇒ id. *)
  let rec to_id : type a m b. (a, m, b) Modality.t -> (a, m, b Modality.id, b) Modalcell.t option =
   fun x ->
    match x with
    | Path (Zero, _) -> Some (Modalcell.id x)
    | Path (Suc (m, g), mode) -> (
        match Modality.Gen.compare g Flat.modality with
        | Eq ->
            let* c = to_id (Path (m, mode)) in
            Some (Modalcell.hcomp (Suc (Zero, g)) Zero c flat_counit)
        | Neq -> (
            match Modality.Gen.compare g Sharp.modality with
            | Neq -> None
            | Eq -> (
                match m with
                | Suc (m', g') -> (
                    match Modality.Gen.compare g' Flat.modality with
                    | Eq ->
                        let* c = to_id (Path (m', mode)) in
                        Some (Modalcell.hcomp (Suc (Suc (Zero, g'), g)) Zero c adj_counit)
                    | Neq -> None)
                | Zero -> None)))

  (* Dually, repeatedly peel an innermost ♯ (via sharp_unit) or an innermost ♯∘♭ pair (via adj_unit) to reach a cell id ⇒ y. *)
  let rec from_id : type a n b. (a, n, b) Modality.t -> (a, b Modality.id, n, b) Modalcell.t option
      =
   fun y ->
    match y with
    | Path (Zero, _) -> Some (Modalcell.id y)
    | Path (Suc (n, h), mode) -> (
        match Modality.Gen.compare h Sharp.modality with
        | Eq ->
            let* c = from_id (Path (n, mode)) in
            Some (Modalcell.hcomp Zero (Suc (Zero, h)) c sharp_unit)
        | Neq -> (
            match Modality.Gen.compare h Flat.modality with
            | Neq -> None
            | Eq -> (
                match n with
                | Suc (n', h') -> (
                    match Modality.Gen.compare h' Sharp.modality with
                    | Eq ->
                        let* c = from_id (Path (n', mode)) in
                        Some (Modalcell.hcomp Zero (Suc (Suc (Zero, h'), h)) c adj_unit)
                    | Neq -> None)
                | Zero -> None)))

  let bridge : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let* cx = to_id x in
    let* cy = from_id y in
    Some (Modalcell.vcomp cy cx)

  let rec find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match Modality.compare x y with
    | Eq -> Some (Modalcell.id x)
    | Neq -> (
        match (x, y) with
        | Path (Suc (m, g), mmode), Path (Suc (n, h), nmode) -> (
            match Modality.Gen.compare g h with
            | Eq ->
                let* c = find_unique (Path (m, mmode)) (Path (n, nmode)) in
                Some (Modalcell.prewhisker (Suc (Zero, g)) (Suc (Zero, h)) c (Modality.of_gen g))
            | Neq -> bridge x y)
        | _ -> bridge x y)

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "cell_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))
end

let install () =
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Flat = Modality.Generate (FlatGen (Testmode)) in
  let module Sharp = Modality.Generate (SharpGen (Testmode)) in
  Modalcell.choose_theory (module SpatialCells (Testmode) (Flat) (Sharp) : Modalcell.Theory)
