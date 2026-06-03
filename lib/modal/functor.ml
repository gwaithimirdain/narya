module DomGen = struct
  let name = "DomType"
end

module CodGen = struct
  let name = "CodType"
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
end

module Functorcell
    (DomMode : Mode.Generated with module G := DomGen)
    (CodMode : Mode.Generated with module G := CodGen)
    (Functor : Modality.Generated with module G := FunctorGen(DomMode)(CodMode)) :
  Modalcell.Theory = struct
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

let install () =
  let module DomMode = Mode.Generate (DomGen) in
  let module CodMode = Mode.Generate (CodGen) in
  let module Functor = Modality.Generate (FunctorGen (DomMode) (CodMode)) in
  Modalcell.choose_theory (module Functorcell (DomMode) (CodMode) (Functor) : Modalcell.Theory)
