open Util

(* We define all the "generator" modules at top-level, but don't call the generation code until the "install" function, so that only one mode theory actually gets installed at runtime.  Thus, each generator module has to be parametrized over the results of generation of the previous ones. *)

module TestmodeGen = struct
  let name = "Type"
end

module ComonadGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = "□"
end

module ComonadCells
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Comonad : Modality.Generated with module G := ComonadGen(Testmode)) =
struct
  type (_, _, _, _) Modalcell.t +=
    | (* The "counit cells" are everything with codomain id, including the identity cell of the identity modality. *)
        Counit_cell :
        ('a, 'mu, 'b) Modality.t
        -> ('a, 'mu, Testmode.t Modality.id, 'b) Modalcell.t
    | (* The other "isomorphism cells" relate any two modalities that are *not* the identity. *)
        Iso_cell :
        (Testmode.t, 'mu, 'a) Modality.t * (Testmode.t, 'nu, 'a) Modality.t
        -> ( Testmode.t,
             ('mu, Comonad.t) Modality.suc,
             ('nu, Comonad.t) Modality.suc,
             'a )
           Modalcell.t

  let find_unique : type a m b c n d.
      (a, m, b) Modality.t ->
      (c, n, d) Modality.t ->
      (a, m, b, c, n, d) Modalcell.find_unique option =
   fun x y ->
    match (x, y) with
    | Path (mu, mu_mode), Path (nu, nu_mode) -> (
        match (Mode.compare mu_mode Testmode.mode, Mode.compare nu_mode Testmode.mode) with
        | Eq, Eq -> (
            match (mu, nu) with
            | Zero, Zero -> Some (Unique (Counit_cell (Modality.id Testmode.mode)))
            | Suc (_, modality), Zero -> (
                match Modality.Gen.compare modality Comonad.modality with
                | Eq -> Some (Unique (Counit_cell (Path (mu, Testmode.mode))))
                | Neq -> failwith "ComonadCells.find_unique: unknown modality")
            | Zero, Suc (_, _) -> None
            | Suc (m', m_modality), Suc (n', n_modality) -> (
                match
                  ( Modality.Gen.compare m_modality Comonad.modality,
                    Modality.Gen.compare n_modality Comonad.modality )
                with
                | Eq, Eq ->
                    Some (Unique (Iso_cell (Path (m', Testmode.mode), Path (n', Testmode.mode))))
                | _ -> failwith "ComonadCells.find_unique: unknown modality"))
        | _ -> failwith "ComonadCells.find_unique: unknown mode")

  let id : type dom modality cod.
      (dom, modality, cod) Modality.t -> (dom, modality, modality, cod) Modalcell.t = function
    | Path (Zero, mode) -> (
        match Mode.compare mode Testmode.mode with
        | Eq -> Counit_cell (Modality.id Testmode.mode)
        | Neq -> failwith "ComonadCells.id: unknown mode")
    | Path (Suc (m, modality), mode) -> (
        match (Mode.compare mode Testmode.mode, Modality.Gen.compare modality Comonad.modality) with
        | Eq, Eq -> Iso_cell (Path (m, Testmode.mode), Path (m, Testmode.mode))
        | Neq, _ -> failwith "ComonadCells.id: unknown mode"
        | _, Neq -> failwith "ComonadCells.id: unknown modality")

  let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
      (dom1, mu1, nu1, cod1) Modalcell.t ->
      (dom2, mu2, nu2, cod2) Modalcell.t ->
      (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
   fun x y ->
    match (x, y) with
    | Counit_cell m, Counit_cell n -> (
        match Modality.compare m n with
        | Eq -> Eq
        | Neq -> Neq)
    | Iso_cell (m, n), Iso_cell (p, q) -> (
        match (Modality.compare m p, Modality.compare n q) with
        | Eq, Eq -> Eq
        | _ -> Neq)
    | _ -> Neq

  let hsrc : type a m n b. (a, m, n, b) Modalcell.t -> a Mode.t = function
    | Counit_cell m -> Modality.src m
    | Iso_cell (m, _) -> Modality.src m
    | _ -> failwith "ComonadCells.hsrc: unknown modal cell"

  let htgt : type a m n b. (a, m, n, b) Modalcell.t -> b Mode.t = function
    | Counit_cell m -> Modality.tgt m
    | Iso_cell (m, _) -> Modality.tgt m
    | _ -> failwith "ComonadCells.htgt: unknown modal cell"

  let vsrc : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, b) Modality.t = function
    | Counit_cell m -> m
    | Iso_cell (m, _) -> Modality.suc m Comonad.modality
    | _ -> failwith "ComonadCells.vsrc: unknown modal cell"

  let vtgt : type a m n b. (a, m, n, b) Modalcell.t -> (a, n, b) Modality.t = function
    | Counit_cell m -> (
        match
          (Mode.compare (Modality.src m) Testmode.mode, Mode.compare (Modality.tgt m) Testmode.mode)
        with
        | Eq, Eq -> Modality.id Testmode.mode
        | _ -> failwith "ComonadCells.vtgt: unknown mode")
    | Iso_cell (_, n) -> Modality.suc n Comonad.modality
    | _ -> failwith "ComonadCells.vtgt: unknown modal cell"

  let hcomp : type a m n b r s c mr ns.
      (a, m, b, r, c, mr) Modality.comp ->
      (a, n, b, s, c, ns) Modality.comp ->
      (b, r, s, c) Modalcell.t ->
      (a, m, n, b) Modalcell.t ->
      (a, mr, ns, c) Modalcell.t =
   fun mr ns x y ->
    match (x, y) with
    | Counit_cell m, Counit_cell r ->
        let Zero = ns in
        let (Comp comp) = Modality.comp r in
        let Eq = Modality.comp_uniq mr comp in
        Counit_cell (Modality.comp_out m comp)
    | _, Iso_cell (m, n) -> (
        match (mr, ns) with
        | Suc (mr', mr_modality), Suc (ns', ns_modality) -> (
            match
              ( Modality.Gen.compare mr_modality Comonad.modality,
                Modality.Gen.compare ns_modality Comonad.modality )
            with
            | Eq, Eq ->
                let (Comp compr) = Modality.comp m in
                let (Comp comps) = Modality.comp n in
                let Eq = Modality.comp_uniq mr' compr in
                let Eq = Modality.comp_uniq ns' comps in
                Iso_cell (Modality.comp_out (vsrc x) compr, Modality.comp_out (vtgt x) comps)
            | _ -> failwith "ComonadCells.hcomp: unknown modality"))
    | Iso_cell (r, s), Counit_cell (Path (Suc (m, m_modality), _)) -> (
        let Zero = ns in
        match mr with
        | Suc (mr', mr_modality) -> (
            match
              ( Modality.Gen.compare m_modality Comonad.modality,
                Modality.Gen.compare mr_modality Comonad.modality )
            with
            | Eq, Eq ->
                let (Comp comp) = Modality.comp (Path (m, Testmode.mode)) in
                let Eq = Modality.comp_uniq mr' comp in
                Iso_cell (Modality.comp_out (Modality.suc r Comonad.modality) comp, s)
            | _ -> failwith "ComonadCells.hcomp: unknown modality"))
    | Iso_cell (r, s), Counit_cell (Path (Zero, _)) ->
        let Zero, Zero = (mr, ns) in
        Iso_cell (r, s)
    | _ -> failwith "ComonadCells.hcomp: unknown modal cell"

  let vcomp : type a m n r b.
      (a, n, r, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> (a, m, r, b) Modalcell.t =
   fun x y ->
    match (x, y) with
    | Counit_cell _, _ -> Counit_cell (vsrc y)
    | Iso_cell (_, n), Iso_cell (m, _) -> Iso_cell (m, n)
    | _ -> failwith "ComonadCells.vcomp: unknown modal cell"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "ε_" ^ string_of_int (Modality.length (vsrc m)) ^ "_" ^ string_of_int (Modality.length (vtgt m))
end

let install () =
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Comonad = Modality.Generate (ComonadGen (Testmode)) in
  Modalcell.set_theory (module ComonadCells (Testmode) (Comonad) : Modalcell.Theory)
