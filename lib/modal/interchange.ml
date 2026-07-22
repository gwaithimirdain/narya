(* A mode theory with three modes AType, BType, CType, two functor generators ▹, ◃ : AType → BType with a generating 2-cell alpha : ▹ ⇒ ◃, and two modality generators ▸, ◂ : BType → CType with a generating 2-cell beta : ▸ ⇒ ◂.  The theory is locally posetal (any two parallel 2-cells are equal).

   There is no modality out of CType or into AType, so the only nonidentity composite modalities are the four length-2 composites ▹▸ (▹ then ▸), ▹◂ (▹ then ◂), ◃▸ (◃ then ▸), ◃◂ (◃ then ◂), all AType → CType.  Whiskering alpha and beta gives four more 2-cells forming a commuting square

       ▹▸ --（alpha whiskered by ▸)--> ◃▸
        |                                |
   (beta whiskered by ▹)          (beta whiskered by ◃)
        |                                |
        v                                v
       ▹◂ --（alpha whiskered by ◂)--> ◃◂

   and the two composites around the square, ▹▸ ⇒ ◃▸ ⇒ ◃◂ and ▹▸ ⇒ ▹◂ ⇒ ◃◂, are the interchange
   law: since the theory is locally posetal they must be (and are declared to be) the same cell
   ▹▸ ⇒ ◃◂. *)

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

module TriGen
    (AMode : Mode.Generated with module G := AGen)
    (BMode : Mode.Generated with module G := BGen) =
struct
  type src = AMode.t
  type tgt = BMode.t

  let src = AMode.mode
  let tgt = BMode.mode
  let name = ref "▹"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TldGen
    (AMode : Mode.Generated with module G := AGen)
    (BMode : Mode.Generated with module G := BGen) =
struct
  type src = AMode.t
  type tgt = BMode.t

  let src = AMode.mode
  let tgt = BMode.mode
  let name = ref "◃"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module RtGen
    (BMode : Mode.Generated with module G := BGen)
    (CMode : Mode.Generated with module G := CGen) =
struct
  type src = BMode.t
  type tgt = CMode.t

  let src = BMode.mode
  let tgt = CMode.mode
  let name = ref "▸"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module LfGen
    (BMode : Mode.Generated with module G := BGen)
    (CMode : Mode.Generated with module G := CGen) =
struct
  type src = BMode.t
  type tgt = CMode.t

  let src = BMode.mode
  let tgt = CMode.mode
  let name = ref "◂"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module InterchangeCell
    (AMode : Mode.Generated with module G := AGen)
    (BMode : Mode.Generated with module G := BGen)
    (CMode : Mode.Generated with module G := CGen)
    (Tri : Modality.Generated with module G := TriGen(AMode)(BMode))
    (Tld : Modality.Generated with module G := TldGen(AMode)(BMode))
    (Rt : Modality.Generated with module G := RtGen(BMode)(CMode))
    (Lf : Modality.Generated with module G := LfGen(BMode)(CMode)) : Modalcell.Theory = struct
  let cmode = CMode.mode
  let tri = Modality.of_gen Tri.modality
  let tld = Modality.of_gen Tld.modality
  let rt = Modality.of_gen Rt.modality
  let lf = Modality.of_gen Lf.modality

  (* The two generating 2-cells, ▹ ⇒ ◃ (over AType → BType) and ▸ ⇒ ◂ (over BType → CType). *)
  let alpha = Modalcell.of_gen (Modalcell.generate "α" tri tld)
  let beta = Modalcell.of_gen (Modalcell.generate "β" rt lf)

  (* The four length-2 composite modalities AType → CType. *)
  let tri_rt = Modality.Path (Suc (Suc (Zero, Rt.modality), Tri.modality), cmode)
  let tri_lf = Modality.Path (Suc (Suc (Zero, Lf.modality), Tri.modality), cmode)
  let tld_rt = Modality.Path (Suc (Suc (Zero, Rt.modality), Tld.modality), cmode)
  let tld_lf = Modality.Path (Suc (Suc (Zero, Lf.modality), Tld.modality), cmode)

  (* The four whiskered 2-cells forming the sides of the interchange square. *)
  let alpha_rt = Modalcell.postwhisker (Suc (Zero, Tri.modality)) (Suc (Zero, Tld.modality)) rt alpha
  let alpha_lf = Modalcell.postwhisker (Suc (Zero, Tri.modality)) (Suc (Zero, Tld.modality)) lf alpha
  let beta_tri = Modalcell.prewhisker (Suc (Zero, Tri.modality)) (Suc (Zero, Tri.modality)) beta tri
  let beta_tld = Modalcell.prewhisker (Suc (Zero, Tld.modality)) (Suc (Zero, Tld.modality)) beta tld

  (* The diagonal ▹▸ ⇒ ◃◂, computed as one of the two (equal, since posetal) composites around the
     square. *)
  let diag = Modalcell.vcomp beta_tld alpha_rt

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
        match (Modality.compare x tri, Modality.compare y tld) with
        | Eq, Eq -> Some alpha
        | _ -> (
            match (Modality.compare x rt, Modality.compare y lf) with
            | Eq, Eq -> Some beta
            | _ -> (
                match (Modality.compare x tri_rt, Modality.compare y tld_rt) with
                | Eq, Eq -> Some alpha_rt
                | _ -> (
                    match (Modality.compare x tri_lf, Modality.compare y tld_lf) with
                    | Eq, Eq -> Some alpha_lf
                    | _ -> (
                        match (Modality.compare x tri_rt, Modality.compare y tri_lf) with
                        | Eq, Eq -> Some beta_tri
                        | _ -> (
                            match (Modality.compare x tld_rt, Modality.compare y tld_lf) with
                            | Eq, Eq -> Some beta_tld
                            | _ -> (
                                match (Modality.compare x tri_rt, Modality.compare y tld_lf) with
                                | Eq, Eq -> Some diag
                                | _ -> None)))))))

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "interchange"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string = fun _ -> "id"
end

let install modes modalities modalcells =
  (match modalcells with
  | [] -> ()
  | _ -> failwith "wrong number of modal cell names for interchange mode theory");
  (match modes with
  | [ a; b; c ] ->
      AGen.name := a;
      BGen.name := b;
      CGen.name := c
  | [] -> ()
  | _ -> failwith "wrong number of mode names for interchange mode theory");
  let module AMode = Mode.Generate (AGen) in
  let module BMode = Mode.Generate (BGen) in
  let module CMode = Mode.Generate (CGen) in
  let module Tri = TriGen (AMode) (BMode) in
  let module Tld = TldGen (AMode) (BMode) in
  let module Rt = RtGen (BMode) (CMode) in
  let module Lf = LfGen (BMode) (CMode) in
  (match modalities with
  | [ tri; tld; rt; lf ] ->
      Tri.name := tri;
      Tld.name := tld;
      Rt.name := rt;
      Lf.name := lf
  | [] -> ()
  | _ -> failwith "wrong number of modality names for interchange mode theory");
  Modality.set_one_char true modalities;
  let module Tri' = Modality.Generate (Tri) in
  let module Tld' = Modality.Generate (Tld) in
  let module Rt' = Modality.Generate (Rt) in
  let module Lf' = Modality.Generate (Lf) in
  Modalcell.choose_theory
    (module InterchangeCell (AMode) (BMode) (CMode) (Tri') (Tld') (Rt') (Lf') : Modalcell.Theory)
