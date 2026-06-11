open Dim

(* We define all the "generator" modules at top-level, but don't call the generation code until the "install" function, so that only one mode theory actually gets installed at runtime.  Thus, each generator module has to be parametrized over the results of generation of the previous ones. *)

module TestmodeGen = struct
  let name = "Type"
end

(* We don't need to generate any modalities; the identity automatically exists. *)

module Idcell (Testmode : Mode.Generated with module G := TestmodeGen) : Modalcell.Theory = struct
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match Modality.compare x y with
    | Eq -> Some (Modalcell.id x)
    | Neq -> None

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = fun _ -> "id"

  let filter_deg : type a m n b x y z.
      (a, m, n, b) Modalcell.t ->
      z D.t ->
      (a, m, b, x, z) Modality.filter_dim ->
      (a, n, b, y, z) Modality.filter_dim ->
      (y, x) deg =
   fun a z fm fn ->
    match Modality.compare (Modalcell.vsrc a) (Modalcell.vtgt a) with
    | Eq ->
        let Eq = Modality.filter_uniq fm fn in
        id_deg (Modality.filtered z fm)
    | Neq -> failwith "nonidentity modal cell in trivial theory"
end

let install () =
  let module Testmode = Mode.Generate (TestmodeGen) in
  Modalcell.choose_theory (module Idcell (Testmode) : Modalcell.Theory)
