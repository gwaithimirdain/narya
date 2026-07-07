open Util
open Dim

(* We define all the "generator" modules at top-level, but don't call the generation code until the "install" function, so that only one mode theory actually gets installed at runtime.  Thus, each generator module has to be parametrized over the results of generation of the previous ones. *)

module TestmodeGen = struct
  let name = "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module CoreflectorGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = "♭"

  type nonparametric = D.one

  let nonparametric = D.one
end

module CoreflectorCells
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Coreflector : Modality.Generated with module G := CoreflectorGen(Testmode)) =
struct
  let comonad = Modality.of_gen Coreflector.modality
  let counit = Modalcell.of_gen (Modalcell.generate comonad (Modality.id Testmode.mode))

  let comult =
    Modalcell.of_gen
      (Modalcell.generate comonad
         (Path (Suc (Suc (Zero, Coreflector.modality), Coreflector.modality), Testmode.mode)))

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

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "ε_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))

  let filter_deg : type a m n b x y z.
      (a, m, n, b) Modalcell.t ->
      z D.t ->
      (a, m, b, x, z) Modality.filter_dim ->
      (a, n, b, y, z) Modality.filter_dim ->
      (y, x) deg =
   fun _ z fm fn ->
    let x = Modality.filtered z fm in
    let y = Modality.filtered z fn in
    match D.compare x y with
    | Eq -> id_deg x
    | Neq -> (
        match D.compare_zero x with
        | Zero -> deg_zero y
        | Pos _ -> failwith "impossible modal cell in nonparametric comonad theory")
end

let install () =
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Coreflector = Modality.Generate (CoreflectorGen (Testmode)) in
  Modalcell.choose_theory (module CoreflectorCells (Testmode) (Coreflector) : Modalcell.Theory)
