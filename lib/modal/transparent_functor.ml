open Dim

module DomGen = struct
  let name = "DomType"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module CodGen = struct
  let name = "CodType"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module FunctorGen
    (DomMode : Mode.Generated with module G := DomGen)
    (CodMode : Mode.Generated with module G := CodGen) =
struct
  type src = DomMode.t
  type tgt = CodMode.t

  let src = DomMode.mode
  let tgt = CodMode.mode
  let name = "○"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module Functorcell
    (DomMode : Mode.Generated with module G := DomGen)
    (CodMode : Mode.Generated with module G := CodGen)
    (Functor : Modality.Generated with module G := FunctorGen(DomMode)(CodMode)) :
  Modalcell.Theory = struct
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

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = fun _ -> "id"
end

module TransparentFunctorModalities : Modality.Theory = struct
  let pellucid _ = false
  let transparent _ = true
  let translucent _ = true
  let tangible _ = true
  let parametric_unlocker _ = false
  let one_char = true
end

let install () =
  let module DomMode = Mode.Generate (DomGen) in
  let module CodMode = Mode.Generate (CodGen) in
  let module Functor = Modality.Generate (FunctorGen (DomMode) (CodMode)) in
  Modalcell.choose_theory (module Functorcell (DomMode) (CodMode) (Functor) : Modalcell.Theory);
  Modality.choose_theory (module TransparentFunctorModalities : Modality.Theory)
