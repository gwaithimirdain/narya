open Util
open Dim

(* We define all the "generator" modules at top-level, but don't call the generation code until the "install" function, so that only one mode theory actually gets installed at runtime.  Thus, each generator module has to be parametrized over the results of generation of the previous ones. *)

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module ReflectorGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♯"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

(* Dual to CoreflectorCells: ♯ is an idempotent monad (a reflector) rather than an idempotent comonad, so it has a unit id ⇒ ♯ and a multiplication ♯∘♯ ⇒ ♯, rather than a counit ♯ ⇒ id and a comultiplication ♯ ⇒ ♯∘♯.  Consequently a 2-cell m ⇒ n exists between two words in ♯ exactly when n is "at least as long as" m: from nothing you can only reach a nonempty word (via the unit, never the reverse), while between any two nonempty words there is always a (unique, since ♯ is idempotent) cell in either direction. *)
module ReflectorCells
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Reflector : Modality.Generated with module G := ReflectorGen(Testmode)) =
struct
  let monad = Modality.of_gen Reflector.modality
  let unit = Modalcell.of_gen (Modalcell.generate (Modality.id Testmode.mode) monad)

  let mult =
    Modalcell.of_gen
      (Modalcell.generate
         (Path (Suc (Suc (Zero, Reflector.modality), Reflector.modality), Testmode.mode))
         monad)

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
    | Path (Zero, _), Path (Suc (n, h), nmode) -> (
        match Modality.Gen.compare h Reflector.modality with
        | Eq ->
            let* c = find_unique x (Path (n, nmode)) in
            Some (Modalcell.hcomp Zero (Suc (Zero, h)) c unit)
        | Neq -> None)
    | Path (Suc (_, _), _), Path (Zero, _) -> None
    | Path (Suc (Suc (m, k), g), mmode), Path (Suc (n, h), nmode) -> (
        match
          ( Modality.Gen.compare g Reflector.modality,
            Modality.Gen.compare k Reflector.modality,
            Modality.Gen.compare h Reflector.modality )
        with
        | Eq, Eq, Eq ->
            let* c = find_unique (Path (m, mmode)) (Path (n, nmode)) in
            Some (Modalcell.hcomp (Suc (Suc (Zero, k), g)) (Suc (Zero, h)) c mult)
        | _ -> None)
    | Path (Suc (m, g), mmode), Path (Suc (n, h), nmode) -> (
        match Modality.Gen.compare g h with
        | Eq ->
            let* c = find_unique (Path (m, mmode)) (Path (n, nmode)) in
            Some (Modalcell.prewhisker (Suc (Zero, g)) (Suc (Zero, h)) c (Modality.of_gen g))
        | Neq -> None)

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "reflector"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "η_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))
end

let install modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for reflector mode theory");
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Sharp = ReflectorGen (Testmode) in
  (match modalities with
  | [ sharp ] -> Sharp.name := sharp
  | [] -> ()
  | _ -> failwith "wrong number of modality names for reflector mode theory");
  Modality.set_one_char true modalities;
  let module Reflector = Modality.Generate (Sharp) in
  Modalcell.choose_theory (module ReflectorCells (Testmode) (Reflector) : Modalcell.Theory)
