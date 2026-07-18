open Dim

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
  val transparent : bool
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "functor"
  let transparent = false
end

module Transparent = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "functor"
  let transparent = true
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete functor"
  let transparent = false
end

module DomGen (V : Variant) = struct
  let name = ref "DomType"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module CodGen = struct
  let name = ref "CodType"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module FunctorGen
    (V : Variant)
    (DomMode : Mode.Generated with module G := DomGen(V))
    (CodMode : Mode.Generated with module G := CodGen) =
struct
  type src = DomMode.t
  type tgt = CodMode.t

  let src = DomMode.mode
  let tgt = CodMode.mode
  let name = ref "○"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module Functorcell
    (V : Variant)
    (DomMode : Mode.Generated with module G := DomGen(V))
    (CodMode : Mode.Generated with module G := CodGen)
    (Functor : Modality.Generated with module G := FunctorGen(V)(DomMode)(CodMode)) :
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

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "functor"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = fun _ -> "id"
end

module FunctorModalities (V : Variant) : Modality.Theory = struct
  let tangible _ = true
  let pellucid _ = false
  let transparent _ = V.transparent
  let translucent _ = true
end

let install (module V : Variant) modes modalities modalcells =
  (match modalcells with
  | [] -> ()
  | _ -> failwith "wrong number of modal cell names for functor mode theory");
  let module Dom = DomGen (V) in
  (match modes with
  | [ dom; cod ] ->
      Dom.name := dom;
      CodGen.name := cod
  | [] -> ()
  | _ -> failwith "wrong number of mode names for functor mode theory");
  let module DomMode = Mode.Generate (Dom) in
  let module CodMode = Mode.Generate (CodGen) in
  let module CircGen = FunctorGen (V) (DomMode) (CodMode) in
  (match modalities with
  | [ circ ] -> CircGen.name := circ
  | [] -> ()
  | _ -> failwith "wrong number of modality names for functor mode theory");
  Modality.set_one_char true modalities;
  let module Functor = Modality.Generate (CircGen) in
  Modalcell.choose_theory (module Functorcell (V) (DomMode) (CodMode) (Functor) : Modalcell.Theory);
  Modality.choose_theory (module FunctorModalities (V) : Modality.Theory)
