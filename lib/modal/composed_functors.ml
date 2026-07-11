(* A mode theory with three modes A, B, C and two composable modality generators F : A → B and G : B → C, with only identity 2-cells.  Used to test that composition of modal operators is preserved. *)

open Dim

module AGen = struct
  let name = ref "AType"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module BGen = struct
  let name = ref "BType"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module CGen = struct
  let name = ref "CType"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module FGen
    (AMode : Mode.Generated with module G := AGen)
    (BMode : Mode.Generated with module G := BGen) =
struct
  type src = AMode.t
  type tgt = BMode.t

  let src = AMode.mode
  let tgt = BMode.mode
  let name = ref "○"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module GGen
    (BMode : Mode.Generated with module G := BGen)
    (CMode : Mode.Generated with module G := CGen) =
struct
  type src = BMode.t
  type tgt = CMode.t

  let src = BMode.mode
  let tgt = CMode.mode
  let name = ref "▱"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module Composedcell : Modalcell.Theory = struct
  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option = function
    | Path (Zero, mode) -> Some (Modalcell.id_sinister mode)
    | _ -> None

  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match Modality.compare x y with
    | Eq -> Some (Modalcell.id x)
    | Neq -> None

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "composed functors"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = fun _ -> "id"
end

let install modes modalities =
  (match modes with
  | [ a; b; c ] ->
      AGen.name := a;
      BGen.name := b;
      CGen.name := c
  | [] -> ()
  | _ -> failwith "wrong number of mode names for composed functors mode theory");
  let module AMode = Mode.Generate (AGen) in
  let module BMode = Mode.Generate (BGen) in
  let module CMode = Mode.Generate (CGen) in
  let module F = FGen (AMode) (BMode) in
  let module G = GGen (BMode) (CMode) in
  (match modalities with
  | [ f; g ] ->
      F.name := f;
      G.name := g
  | [] -> ()
  | _ -> failwith "wrong number of modality names for composed functors mode theory");
  Modality.set_one_char true modalities;
  let module _ = Modality.Generate (F) in
  let module _ = Modality.Generate (G) in
  Modalcell.choose_theory (module Composedcell : Modalcell.Theory)
