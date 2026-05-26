open Util

(* We define all the "generator" modules at top-level, but don't call the generation code until the "install" function, so that only one mode theory actually gets installed at runtime.  Thus, each generator module has to be parametrized over the results of generation of the previous ones. *)

module TestmodeGen = struct
  let name = "Type"
end

(* We don't need to generate any modalities; the identity automatically exists. *)

module Idcell (Testmode : Mode.Generated with module G := TestmodeGen) : Modalcell.Theory = struct
  type (_, _, _, _) Modalcell.t +=
    | Id_cell : (Testmode.t, Testmode.t Modality.id, Testmode.t Modality.id, Testmode.t) Modalcell.t

  let id : type dom modality cod.
      (dom, modality, cod) Modality.t -> (dom, modality, modality, cod) Modalcell.t = function
    | Path (Zero, mode) -> (
        match Mode.compare mode Testmode.mode with
        | Eq -> Id_cell
        | Neq -> failwith "Idcell.id: unknown mode")
    | _ -> failwith "Idcell.id: unknown modality"

  let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
      (dom1, mu1, nu1, cod1) Modalcell.t ->
      (dom2, mu2, nu2, cod2) Modalcell.t ->
      (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> Eq
    | _ -> failwith "Idcell.compare: unknown modal cell"

  let hsrc : type a m n b. (a, m, n, b) Modalcell.t -> a Mode.t = function
    | Id_cell -> Testmode.mode
    | _ -> failwith "Idcell.hsrc: unknown modal cell"

  let htgt : type a m n b. (a, m, n, b) Modalcell.t -> b Mode.t = function
    | Id_cell -> Testmode.mode
    | _ -> failwith "Idcell.htgt: unknown modal cell"

  let vsrc : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, b) Modality.t = function
    | Id_cell -> Path (Zero, Testmode.mode)
    | _ -> failwith "Idcell.vsrc: unknown modal cell"

  let vtgt : type a m n b. (a, m, n, b) Modalcell.t -> (a, n, b) Modality.t = function
    | Id_cell -> Path (Zero, Testmode.mode)
    | _ -> failwith "Idcell.vtgt: unknown modal cell"

  let hcomp : type a m n b r s c mr ns.
      (a, m, b, r, c, mr) Modality.comp ->
      (a, n, b, s, c, ns) Modality.comp ->
      (b, r, s, c) Modalcell.t ->
      (a, m, n, b) Modalcell.t ->
      (a, mr, ns, c) Modalcell.t =
   fun mr ns x y ->
    match (mr, ns, x, y) with
    | Zero, Zero, Id_cell, Id_cell -> Id_cell
    | _ -> failwith "Idcell.hcomp: unknown modal cell"

  let vcomp : type a m n r b.
      (a, n, r, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> (a, m, r, b) Modalcell.t =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> Id_cell
    | _ -> failwith "Idcell.vcomp: unknown modal cell"

  let find_unique : type a m b c n d.
      (a, m, b) Modality.t ->
      (c, n, d) Modality.t ->
      (a, m, b, c, n, d) Modalcell.find_unique option =
   fun x y ->
    match (x, y) with
    | Path (Zero, xmode), Path (Zero, ymode) -> (
        match (Mode.compare xmode Testmode.mode, Mode.compare ymode Testmode.mode) with
        | Eq, Eq -> Some (Unique Id_cell)
        | _ -> None)
    | _ -> None

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = function
    | Id_cell -> "id"
    | _ -> failwith "Idcell.to_string: unknown modal cell"
end

let install () =
  let module Testmode = Mode.Generate (TestmodeGen) in
  Modalcell.set_theory (module Idcell (Testmode) : Modalcell.Theory)
