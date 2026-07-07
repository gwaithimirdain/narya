(* A mode theory with three modes A, B, C and two composable modality generators F : A → B and G : B → C, with only identity 2-cells.  Used to test that composition of modal operators is preserved. *)

open Dim

module AGen = struct
  let name = "AType"
end

module BGen = struct
  let name = "BType"
end

module CGen = struct
  let name = "CType"
end

module FGen
    (AMode : Mode.Generated with module G := AGen)
    (BMode : Mode.Generated with module G := BGen) =
struct
  type src = AMode.t
  type tgt = BMode.t

  let src = AMode.mode
  let tgt = BMode.mode
  let name = "F"

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
  let name = "G"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module Composedcell : Modalcell.Theory = struct
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match Modality.compare x y with
    | Eq -> Some (Modalcell.id x)
    | Neq -> None

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = fun _ -> "id"
end

(* Like arbitrary functors, F and G and their composites are transparent and translucent but not pellucid; identity modalities are always pellucid. *)
module Composedmodality : Modality.Theory = struct
  let sharp _ = true

  let pellucid : type a m b. (a, m, b) Modality.t -> bool =
   fun m ->
    match Modality.compare_id m with
    | Eq -> true
    | Neq -> false

  let transparent _ = true
  let translucent _ = true
end

let install () =
  let module AMode = Mode.Generate (AGen) in
  let module BMode = Mode.Generate (BGen) in
  let module CMode = Mode.Generate (CGen) in
  let module _ = Modality.Generate (FGen (AMode) (BMode)) in
  let module _ = Modality.Generate (GGen (BMode) (CMode)) in
  Modalcell.choose_theory (module Composedcell : Modalcell.Theory);
  Modality.choose_theory (module Composedmodality : Modality.Theory)
