open Dim

(* A single mode Type with a single endomodality "flat" equipped with a comonad structure: a
   counit ε : flat ⇒ id and a comultiplication δ : flat ⇒ flat∘flat, satisfying the comonad laws
   (counit laws and coassociativity) and nothing else -- in particular, flat is *not* declared
   idempotent (there is no cell or isomorphism flat∘flat ⇒ flat), so this is the free comonad on a
   single endofunctor, not (as with Coreflector) an idempotent one.

   Consequently the theory is not locally posetal: parallel 2-cells can differ.  Since the only
   generator is flat, every modality is just flatⁿ for some n, and (by coassociativity collapsing
   all parenthesizations, and by the two counit laws each cancelling a bare flat introduced next to
   a leaf) a 2-cell flatᵃ ⇒ flatᵇ is uniquely determined by an ordered "composition" of b into a
   nonnegative parts k₁,...,kₐ (the number of cells is the binomial coefficient C(a+b-1,a-1)): the
   i-th input is split, via a canonically-associated chain of comultiplications, into kᵢ of the b
   outputs (or, if kᵢ = 0, deleted via the counit), and the groups tile the outputs in order.  Two
   parallel cells are equal exactly when they induce the same sequence (k₁,...,kₐ); this is
   witnessed directly (not via the Pairing module, which is specific to the "cup/cap" combinatorics
   of a free adjunction's unit/counit, not the "branching" combinatorics of a comonad's counit/comult).

   Consequently there is a unique 2-cell flatᵃ ⇒ flatᵇ exactly when a=0=b (identity), or b=0 (the
   unique all-counit cell, any a), or a=1 (the unique canonical b-fold comultiplication); in every
   other case (a≥2 and b≥1, or a=0 and b≥1) there are respectively many or zero cells, so
   find_unique correctly returns None (forcing the user to disambiguate explicitly) or None (no
   such cell) respectively. *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
  val locker : bool
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "comonad"
  let locker = false
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete comonad"
  let locker = true
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

module ComonadCells
    (V : Variant)
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Flat : Modality.Generated with module G := FlatGen(V)(Testmode)) =
struct
  let typ = Testmode.mode
  let flat = Modality.of_gen Flat.modality
  let flatflat = Modality.Path (Suc (Suc (Zero, Flat.modality), Flat.modality), typ)
  let counit_gen = Modalcell.generate "ε" flat (Modality.id typ)
  let comult_gen = Modalcell.generate "δ" flat flatflat
  let counit = Modalcell.of_gen counit_gen
  let comult = Modalcell.of_gen comult_gen

  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option = function
    | Path (Zero, mode) -> Some (Modalcell.id_sinister mode)
    | _ -> None

  (* The invariant of a 2-cell: the sequence (k₁,...,kₐ), a=length of the domain word, recording
     how many of the codomain generators (in order) each domain generator expands into. *)
  let rec signature : type a m n b. (a, m, n, b) Modalcell.t -> int list = function
    | Modalcell.Id m -> List.init (Modality.length m) (fun _ -> 1)
    | Modalcell.Gen g -> (
        match Modalcell.Gen.compare g counit_gen with
        | Eq -> [ 0 ]
        | Neq -> (
            match Modalcell.Gen.compare g comult_gen with
            | Eq -> [ 2 ]
            | Neq -> failwith "comonad: unrecognized generating 2-cell"))
    | Modalcell.Hcomp (_, _, y, x) -> signature x @ signature y
    | Modalcell.Vcomp (y, x) ->
        (* Partition y's sequence into groups whose sizes are given by x's sequence, and sum each
           group, to get the composite's sequence. *)
        let rec partition xs ys =
          match xs with
          | [] -> []
          | k :: xs' ->
              let grp = List.filteri (fun i _ -> i < k) ys in
              let rest = List.filteri (fun i _ -> i >= k) ys in
              List.fold_left ( + ) 0 grp :: partition xs' rest in
        partition (signature x) (signature y)

  (* Two parallel 2-cells are equal exactly when they induce the same sequence. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun c1 c2 -> signature c1 = signature c2

  (* The unique cell flatᵃ ⇒ id, for any a, killing each input with the counit. *)
  let rec chain_counit : type a m b. (a, m, b) Modality.t -> (a, m, b Modality.id, b) Modalcell.t =
   fun md ->
    match md with
    | Path (Zero, mode) -> Modalcell.id2 mode
    | Path (Suc (inner, g), mode) -> (
        match Modality.Gen.compare g Flat.modality with
        | Neq -> failwith "comonad: unrecognized generator"
        | Eq ->
            let rest = chain_counit (Modality.Path (inner, mode)) in
            Modalcell.hcomp (Suc (Zero, g)) Zero rest counit)

  (* The unique cell flat ⇒ n, for any n = flatᵇ, splitting the single input into b outputs via a
     canonically-associated chain of comultiplications (the leading output is left alone and the
     rest is split further, recursing on n's tail; coassociativity means any other association
     would give an equal, though not identical, cell). *)
  let rec chain_comult : type n.
      (Testmode.t, n, Testmode.t) Modality.t -> (Testmode.t, _, n, Testmode.t) Modalcell.t =
   fun n ->
    match n with
    | Path (Zero, _) -> counit
    | Path (Suc (Zero, g), _) -> (
        match Modality.Gen.compare g Flat.modality with
        | Neq -> failwith "comonad: unrecognized generator"
        | Eq -> Modalcell.id flat)
    | Path (Suc (inner, g), mode) -> (
        match Modality.Gen.compare g Flat.modality with
        | Neq -> failwith "comonad: unrecognized generator"
        | Eq ->
            let rest = chain_comult (Modality.Path (inner, mode)) in
            let step = Modalcell.hcomp (Suc (Zero, g)) (Suc (Zero, g)) rest (Modalcell.id flat) in
            Modalcell.vcomp step comult)

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match y with
    | Path (Zero, _) -> (
        match x with
        | Path (Zero, _) -> Some (Modalcell.id x)
        | Path (Suc (_, _), _) -> Some (chain_counit x))
    | Path (Suc (_, _), _) -> (
        match x with
        | Path (Zero, _) -> None
        | Path (Suc (Zero, g), _) -> (
            match Modality.Gen.compare g Flat.modality with
            | Neq -> None
            | Eq -> Some (chain_comult y))
        | Path (Suc (Suc (_, _), _), _) -> None)

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun m ->
    if V.locker then
      match Mode.compare m Testmode.mode with
      | Eq -> Ok (Modalcell.Locker (flat, counit))
      | Neq -> Ok (Locker (Modality.id m, Id (Modality.id m)))
    else Error "comonad"

  (* Since parallel 2-cells can differ, we display a cell by its signature. *)
  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun c -> "[" ^ String.concat "," (List.map string_of_int (signature c)) ^ "]"
end

let install (module V : Variant) modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith ("wrong number of mode names for " ^ V.name ^ " mode theory"));
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Flat = FlatGen (V) (Testmode) in
  (match modalities with
  | [ flat ] -> Flat.name := flat
  | [] -> ()
  | _ -> failwith ("wrong number of modality names for " ^ V.name ^ " mode theory"));
  Modality.set_one_char true modalities;
  let module Flat = Modality.Generate (Flat) in
  Modalcell.choose_theory (module ComonadCells (V) (Testmode) (Flat) : Modalcell.Theory)
