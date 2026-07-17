(* A mode theory with two modes DomMode and CodMode and three modality generators ○, ▱, ▷ : DomMode → CodMode, together with two generating 2-cells alpha : ○ ⇒ ▱ and beta : ▱ ⇒ ▷ (and no others).  The theory is locally posetal (any two parallel 2-cells are equal), so the vertical composite beta∘alpha : ○ ⇒ ▷ is *the* unique 2-cell from ○ to ▷, without needing to be declared as a separate generator.  Since there is no modality from CodMode back to DomMode, the only modalities are the two identities, ○, ▱, and ▷: there are no nontrivial composite modalities to normalize. *)

open Dim

module DomGen = struct
  let name = ref "DomMode"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module CodGen = struct
  let name = ref "CodMode"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module CircGen
    (DomMode : Mode.Generated with module G := DomGen)
    (CodMode : Mode.Generated with module G := CodGen) =
struct
  type src = DomMode.t
  type tgt = CodMode.t

  let src = DomMode.mode
  let tgt = CodMode.mode
  let name = ref "○"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module BoxGen
    (DomMode : Mode.Generated with module G := DomGen)
    (CodMode : Mode.Generated with module G := CodGen) =
struct
  type src = DomMode.t
  type tgt = CodMode.t

  let src = DomMode.mode
  let tgt = CodMode.mode
  let name = ref "▱"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TriGen
    (DomMode : Mode.Generated with module G := DomGen)
    (CodMode : Mode.Generated with module G := CodGen) =
struct
  type src = DomMode.t
  type tgt = CodMode.t

  let src = DomMode.mode
  let tgt = CodMode.mode
  let name = ref "▷"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module ComposableTransformationsCell
    (DomMode : Mode.Generated with module G := DomGen)
    (CodMode : Mode.Generated with module G := CodGen)
    (Circle : Modality.Generated with module G := CircGen(DomMode)(CodMode))
    (Box : Modality.Generated with module G := BoxGen(DomMode)(CodMode))
    (Tri : Modality.Generated with module G := TriGen(DomMode)(CodMode)) : Modalcell.Theory =
struct
  let circ = Modality.of_gen Circle.modality
  let box = Modality.of_gen Box.modality
  let tri = Modality.of_gen Tri.modality

  (* The two generating 2-cells, ○ ⇒ ▱ and ▱ ⇒ ▷. *)
  let alpha = Modalcell.of_gen (Modalcell.generate "α" circ box)
  let beta = Modalcell.of_gen (Modalcell.generate "β" box tri)

  (* The derived composite ○ ⇒ ▷, obtained by vertically composing alpha and beta rather than by
     a separate generator; since the theory is locally posetal this is automatically *the* unique
     cell of this source and target. *)
  let gamma = Modalcell.vcomp beta alpha

  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option = function
    | Path (Zero, mode) -> Some (Modalcell.id_sinister mode)
    | _ -> None

  (* Locally posetal: any two parallel 2-cells are equal. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match Modality.compare x y with
    | Eq -> Some (Modalcell.id x)
    | Neq -> (
        match (Modality.compare x circ, Modality.compare y box) with
        | Eq, Eq -> Some alpha
        | _ -> (
            match (Modality.compare x box, Modality.compare y tri) with
            | Eq, Eq -> Some beta
            | _ -> (
                match (Modality.compare x circ, Modality.compare y tri) with
                | Eq, Eq -> Some gamma
                | _ -> None)))

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "composable transformations"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = fun _ -> "id"
end

let install modes modalities =
  (match modes with
  | [ dom; cod ] ->
      DomGen.name := dom;
      CodGen.name := cod
  | [] -> ()
  | _ -> failwith "wrong number of mode names for composable transformations mode theory");
  let module DomMode = Mode.Generate (DomGen) in
  let module CodMode = Mode.Generate (CodGen) in
  let module Circ = CircGen (DomMode) (CodMode) in
  let module Box = BoxGen (DomMode) (CodMode) in
  let module Tri = TriGen (DomMode) (CodMode) in
  (match modalities with
  | [ circ; box; tri ] ->
      Circ.name := circ;
      Box.name := box;
      Tri.name := tri
  | [] -> ()
  | _ -> failwith "wrong number of modality names for composable transformations mode theory");
  Modality.set_one_char true modalities;
  let module Circle = Modality.Generate (Circ) in
  let module Box' = Modality.Generate (Box) in
  let module Tri' = Modality.Generate (Tri) in
  Modalcell.choose_theory
    (module ComposableTransformationsCell (DomMode) (CodMode) (Circle) (Box') (Tri') :
      Modalcell.Theory)
