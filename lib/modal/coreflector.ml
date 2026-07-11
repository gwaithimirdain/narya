open Util
open Dim

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "coreflector"
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete coreflector"
end

(* We define all the "generator" modules at top-level, but don't call the generation code until the "install" function, so that only one mode theory actually gets installed at runtime.  Thus, each generator module has to be parametrized over the results of generation of the previous ones. *)

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module CoreflectorGen (V : Variant) (Testmode : Mode.Generated with module G := TestmodeGen) =
struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♭"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module CoreflectorCells
    (V : Variant)
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Coreflector : Modality.Generated with module G := CoreflectorGen(V)(Testmode)) =
struct
  let comonad = Modality.of_gen Coreflector.modality
  let counit = Modalcell.of_gen (Modalcell.generate comonad (Modality.id Testmode.mode))

  let comult =
    Modalcell.of_gen
      (Modalcell.generate comonad
         (Path (Suc (Suc (Zero, Coreflector.modality), Coreflector.modality), Testmode.mode)))

  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option = function
    | Path (Zero, mode) -> Some (Modalcell.id_sinister mode)
    | _ -> None

  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  let rec find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let open Monad.Ops (Monad.Maybe) in
    match (x, y) with
    | Path (Zero, _), Path (Zero, _) -> Some (Modalcell.id x)
    | Path (Suc (m, g), mode), Path (Zero, _) -> (
        match Modality.Gen.compare g Coreflector.modality with
        | Eq ->
            let* x = find_unique (Path (m, mode)) y in
            Some (Modalcell.hcomp (Suc (Zero, g)) Zero x counit)
        | Neq -> None)
    | Path (Zero, _), Path (Suc (_, _), _) -> None
    | Path (Suc (m, g), mmode), Path (Suc (Suc (n, k), h), nmode) -> (
        match
          ( Modality.Gen.compare g Coreflector.modality,
            Modality.Gen.compare k Coreflector.modality,
            Modality.Gen.compare h Coreflector.modality )
        with
        | Eq, Eq, Eq ->
            let* x = find_unique (Path (m, mmode)) (Path (n, nmode)) in
            Some (Modalcell.hcomp (Suc (Zero, g)) (Suc (Suc (Zero, k), h)) x comult)
        | _ -> None)
    | Path (Suc (m, g), mmode), Path (Suc (n, h), nmode) -> (
        match Modality.Gen.compare g h with
        | Eq ->
            let* x = find_unique (Path (m, mmode)) (Path (n, nmode)) in
            Some (Modalcell.prewhisker (Suc (Zero, g)) (Suc (Zero, h)) x (Modality.of_gen g))
        | Neq -> None)

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "coreflector"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "ε_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))
end

let install (module V : Variant) modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith ("wrong number of mode names for " ^ V.name ^ " mode theory"));
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Flat = CoreflectorGen (V) (Testmode) in
  (match modalities with
  | [ flat ] -> Flat.name := flat
  | [] -> ()
  | _ -> failwith ("wrong number of modality names for " ^ V.name ^ " mode theory"));
  Modality.set_one_char true modalities;
  let module Coreflector = Modality.Generate (Flat) in
  Modalcell.choose_theory (module CoreflectorCells (V) (Testmode) (Coreflector) : Modalcell.Theory)
