(* We define all the "generator" modules at top-level, but don't call the generation code until the "install" function, so that only one mode theory actually gets installed at runtime.  Thus, each generator module has to be parametrized over the results of generation of the previous ones. *)

open Dim

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

(* We don't need to generate any modalities; the identity automatically exists. *)

module Idcell (Testmode : Mode.Generated with module G := TestmodeGen) : Modalcell.Theory = struct
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

let install modes modalities =
  (match modes with
  | [ name ] -> TestmodeGen.name := name
  | [] -> ()
  | _ -> failwith "wrong number of mode names for trivial mode theory");
  (match modalities with
  | [] -> ()
  | _ -> failwith "wrong number of modality names for trivial mode theory");
  let module Testmode = Mode.Generate (TestmodeGen) in
  Modalcell.choose_theory (module Idcell (Testmode) : Modalcell.Theory)
