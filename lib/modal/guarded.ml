open Dim

(* A coreflection (as in Coreflection) with an added endomodality "later" on Timed, a generating
   2-cell "next : id ⇒ later", and an isomorphism "box.later ≅ box" (i.e. □∘later ≅ □).  The theory
   is locally posetal.

   Every composite modality is isomorphic to exactly one normal form: id_Type, laterᵃ (a≥0,
   Timed→Timed, a=0 being id_Timed), a·laterᵃ (△ followed by a≥0 laters, Type→Timed), box (Timed→Type),
   or ab·laterᵃ (tribox = □ then △, followed by a≥0 laters, Timed→Timed).  This is because: (1) the
   only reduction not involving later is □∘△ ≅ id_Type (as in Coreflection); (2) later can compose
   with itself freely (no relation collapses laterᵃ for different a); and (3) any run of laters
   immediately followed by □ collapses entirely, via box.later≅box iterated -- so laters only
   survive at the very end of a normal form (after everything else), never immediately before a □.
   *)

module TypeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TimedGen = struct
  let name = ref "Timed"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TriangleGen
    (Type : Mode.Generated with module G := TypeGen)
    (Timed : Mode.Generated with module G := TimedGen) =
struct
  type src = Type.t
  type tgt = Timed.t

  let src = Type.mode
  let tgt = Timed.mode
  let name = ref "△"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module BoxGen
    (Type : Mode.Generated with module G := TypeGen)
    (Timed : Mode.Generated with module G := TimedGen) =
struct
  type src = Timed.t
  type tgt = Type.t

  let src = Timed.mode
  let tgt = Type.mode
  let name = ref "□"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module LaterGen (Timed : Mode.Generated with module G := TimedGen) = struct
  type src = Timed.t
  type tgt = Timed.t

  let src = Timed.mode
  let tgt = Timed.mode
  let name = ref "▸"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module GuardedCells
    (Type : Mode.Generated with module G := TypeGen)
    (Timed : Mode.Generated with module G := TimedGen)
    (Triangle : Modality.Generated with module G := TriangleGen(Type)(Timed))
    (Box : Modality.Generated with module G := BoxGen(Type)(Timed))
    (Later : Modality.Generated with module G := LaterGen(Timed)) =
struct
  let disc = Type.mode
  let typ = Timed.mode

  (* The three generating modalities. *)
  let tri = Modality.of_gen Triangle.modality
  let box = Modality.of_gen Box.modality
  let later = Modality.of_gen Later.modality

  (* The two-generator composite modalities. *)
  let tribox = Modality.Path (Suc (Suc (Zero, Triangle.modality), Box.modality), typ)
  let boxtri = Modality.Path (Suc (Suc (Zero, Box.modality), Triangle.modality), disc)
  let box_later = Modality.Path (Suc (Suc (Zero, Box.modality), Later.modality), disc)

  (* The generating 2-cells.
       box_counit : △□ ⇒ id_Timed
       box_unit : id_Type ⇒ □△ (iso)        box_unit_inv : □△ ⇒ id_Type
       next : id_Timed ⇒ ▸
       box_later_iso : □▸ ⇒ □ (iso)          box_later_iso_inv : □ ⇒ □▸
  *)
  let box_counit = Modalcell.of_gen (Modalcell.generate "ε" tribox (Modality.id typ))
  let box_unit = Modalcell.of_gen (Modalcell.generate "η" (Modality.id disc) boxtri)
  let box_unit_inv = Modalcell.of_gen (Modalcell.generate "η⁻¹" boxtri (Modality.id disc))
  let next = Modalcell.of_gen (Modalcell.generate "next" (Modality.id typ) later)
  let box_later_iso = Modalcell.of_gen (Modalcell.generate "ε▸" box_later box)
  let box_later_iso_inv = Modalcell.of_gen (Modalcell.generate "ε▸⁻¹" box box_later)

  (* A modality is sinister (a declared left adjoint) if it is the identity or △ (left adjoint to
     □).  Later is not declared as an adjoint. *)
  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match (Modality.compare_id f, Modality.compare f tri) with
    | Eq, _ -> Some (Modalcell.id_sinister (Modality.src f))
    | _, Eq ->
        (* △ ⊣ □ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = tri;
                  right = box;
                  right_left = Suc (Zero, Triangle.modality);
                  unit = box_unit;
                  left_right = Suc (Zero, Box.modality);
                  counit = box_counit;
                }))
    | _ -> None

  (* Locally posetal: any two parallel 2-cells are equal. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun _ _ -> true

  (* The normalization of a modality: an isomorphic normal form together with the isomorphism (in
     both directions).  Every modality is isomorphic to exactly one of: id_Type, laterᵃ (a≥0),
     △·laterᵃ (a≥0), box, or (□△)·laterᵃ (a≥0). *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  (* Prepend a generator g (on the source side, i.e. applied first) to an already-normalized
     modality nf, and renormalize.  There are two kinds of reduction: △ meeting a leading □
     (△·□ ≅ id_Type, exactly as in Coreflection), and later meeting a leading □ (□·later ≅ □,
     absorbed).  In both cases, whatever follows the leading □ in nf (its "rest") is carried along
     unchanged by postwhiskering.  Prepending later onto anything that does NOT start with □ (i.e.
     onto id_Timed or an existing run of laters) simply extends the run by one, with no reduction
     since laters never collapse into each other. *)
  let prepend : type c gg a nf b gm.
      (c, gg, a) Modality.Gen.t ->
      (a, nf, b) Modality.t ->
      (c, gm, (nf, gg) Modality.suc, b) Modalcell.t ->
      (c, (nf, gg) Modality.suc, gm, b) Modalcell.t ->
      (c, gm, b) normalize =
   fun g nf g_to g_from ->
    match
      ( Modality.Gen.compare g Triangle.modality,
        Modality.Gen.compare g Box.modality,
        Modality.Gen.compare g Later.modality )
    with
    | Eq, _, _ -> (
        (* g = △ *)
        match Modality.compare nf (Modality.id typ) with
        | Eq -> Normalize (tri, g_to, g_from) (* △·id_Timed = △ *)
        | Neq -> (
            match nf with
            | Path (Suc (rest_comp, g'), tgt) -> (
                match Modality.Gen.compare g' Box.modality with
                | Eq ->
                    (* nf starts with □ (nf = box or (□△)·laterᵃ); △·□·rest ≅ rest, using △·□≅id *)
                    let rest = Modality.Path (rest_comp, tgt) in
                    let tc =
                      Modalcell.postwhisker
                        (Suc (Suc (Zero, Box.modality), Triangle.modality))
                        Zero rest box_unit_inv in
                    let tcr =
                      Modalcell.postwhisker Zero
                        (Suc (Suc (Zero, Box.modality), Triangle.modality))
                        rest box_unit in
                    Normalize (rest, Modalcell.vcomp tc g_to, Modalcell.vcomp g_from tcr)
                | Neq ->
                    (* nf = laterᵃ (a≥1); △·laterᵃ = △·laterᵃ, no reduction *)
                    Normalize (Modality.suc nf Triangle.modality, g_to, g_from))
            | Path (Zero, _) -> failwith "guarded: unreachable (△·id_Timed already handled)"))
    | _, Eq, _ -> (
        (* g = □ *)
        match Modality.compare nf (Modality.id disc) with
        | Eq -> Normalize (box, g_to, g_from) (* □·id_Type = □ *)
        | Neq -> (
            match nf with
            | Path (Suc (_, g'), _) -> (
                match Modality.Gen.compare g' Triangle.modality with
                | Eq ->
                    (* nf = △·laterᵃ; □·△·laterᵃ = (□△)·laterᵃ, no reduction *)
                    Normalize (Modality.suc nf Box.modality, g_to, g_from)
                | Neq -> failwith "guarded: ill-typed modality composite in normalize (□ case)")
            | Path (Zero, _) -> failwith "guarded: unreachable (□·id_Type already handled)"))
    | _, _, Eq -> (
        (* g = later *)
        match nf with
        | Path (Suc (rest_comp, g'), tgt) -> (
            match Modality.Gen.compare g' Box.modality with
            | Eq ->
                (* nf starts with □ (nf = box or (□△)·laterᵃ); later·□·rest ≅ □·rest, absorbed *)
                let rest = Modality.Path (rest_comp, tgt) in
                let tc =
                  Modalcell.postwhisker
                    (Suc (Suc (Zero, Box.modality), Later.modality))
                    (Suc (Zero, Box.modality))
                    rest box_later_iso in
                let tcr =
                  Modalcell.postwhisker
                    (Suc (Zero, Box.modality))
                    (Suc (Suc (Zero, Box.modality), Later.modality))
                    rest box_later_iso_inv in
                Normalize (nf, Modalcell.vcomp tc g_to, Modalcell.vcomp g_from tcr)
            | Neq ->
                (* nf = laterᵃ (a≥1); extend to laterᵃ⁺¹ *)
                Normalize (Modality.suc nf Later.modality, g_to, g_from))
        | Path (Zero, _) ->
            (* nf = id_Timed; extend to later¹ *)
            Normalize (Modality.suc nf Later.modality, g_to, g_from))
    | _ -> failwith "guarded: unrecognized generator in normalize"

  let rec normalize : type a m b. (a, m, b) Modality.t -> (a, m, b) normalize =
   fun md ->
    match md with
    | Path (Zero, mode) -> Normalize (Modality.id mode, Modalcell.id2 mode, Modalcell.id2 mode)
    | Path (Suc (inner, g), tgt) ->
        let (Normalize (nf, to_nf, from_nf)) = normalize (Path (inner, tgt)) in
        let g_to = Modalcell.prewhisker (Suc (Zero, g)) (Suc (Zero, g)) to_nf (Modality.of_gen g) in
        let g_from =
          Modalcell.prewhisker (Suc (Zero, g)) (Suc (Zero, g)) from_nf (Modality.of_gen g) in
        prepend g nf g_to g_from

  (* A bridge between two "pure" runs of later (laterᵖ ⇒ laterᵍ), which exists iff p≤q, built by
     iteratively extending laterᵖ by one more later (via "next" postwhiskered by the
     already-reached run) until it reaches laterᵍ. *)
  let rec later_run_bridge : type p q.
      (Timed.t, p, Timed.t) Modality.t ->
      (Timed.t, q, Timed.t) Modality.t ->
      (Timed.t, p, q, Timed.t) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match n with
        | Path (Zero, _) -> None
        | Path (Suc (inner, g), tgt) -> (
            match Modality.Gen.compare g Later.modality with
            | Neq -> None
            | Eq -> (
                let n' = Modality.Path (inner, tgt) in
                match later_run_bridge m n' with
                | Some prev ->
                    let step = Modalcell.postwhisker Zero (Suc (Zero, Later.modality)) n' next in
                    Some (Modalcell.vcomp step prev)
                | None -> None)))

  (* The unique 2-cell between two *normal-form* modalities, if one exists.  The only nonidentity
     bridges are: tribox ⇒ id_Timed (box_counit), and, for the "later"-extended families, whatever
     is induced from that plus the later_run_bridge. *)
  let bridge : type a p q b.
      (a, p, b) Modality.t -> (a, q, b) Modality.t -> (a, p, q, b) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match Mode.compare (Modality.tgt m) typ with
        | Neq ->
            (* target Type: the only normal form is id_Type, so m=n=id_Type, already handled *)
            None
        | Eq -> (
            (* target Timed: m,n are each either a pure later-run, △·laterᵃ (source Type), or
               (□△)·laterᵃ (source Timed). *)
            match m with
            | Path (Suc (m_rest, mg), _) -> (
                match Modality.Gen.compare mg Triangle.modality with
                | Eq -> (
                    (* m = △·laterᵃ; n must be of the same shape (same source Type), so its
                       leading generator (the only one with source Type) is also △ *)
                    match n with
                    | Path (Suc (n_rest, ng), _) -> (
                        match Modality.Gen.compare ng Triangle.modality with
                        | Neq -> None
                        | Eq -> (
                            let m' = Modality.Path (m_rest, typ) in
                            let n' = Modality.Path (n_rest, typ) in
                            match later_run_bridge m' n' with
                            | Some cell ->
                                Some
                                  (Modalcell.prewhisker
                                     (Suc (Zero, Triangle.modality))
                                     (Suc (Zero, Triangle.modality))
                                     cell tri)
                            | None -> None))
                    | Path (Zero, _) -> None)
                | Neq -> (
                    match Modality.Gen.compare mg Box.modality with
                    | Eq -> (
                        (* m = (□△)·laterᵃ = tribox·laterᵃ *)
                        match m with
                        | Path (Suc (Suc (m_rest2, mg2), _), _) -> (
                            match Modality.Gen.compare mg2 Triangle.modality with
                            | Neq -> None
                            | Eq -> (
                                let m' = Modality.Path (m_rest2, typ) in
                                (* m' is laterᵃ; box_counit postwhiskered by m' gives m ⇒ m' *)
                                let to_later =
                                  Modalcell.postwhisker
                                    (Suc (Suc (Zero, Triangle.modality), Box.modality))
                                    Zero m' box_counit in
                                match n with
                                | Path (Suc (n_rest, ng), _) -> (
                                    match Modality.Gen.compare ng Box.modality with
                                    | Eq -> (
                                        (* n = tribox·laterᵇ too: bridge the later-runs,
                                           prewhiskered by tribox *)
                                        match n with
                                        | Path (Suc (Suc (n_rest2, ng2), _), _) -> (
                                            match Modality.Gen.compare ng2 Triangle.modality with
                                            | Neq -> None
                                            | Eq -> (
                                                let n' = Modality.Path (n_rest2, typ) in
                                                match later_run_bridge m' n' with
                                                | Some cell ->
                                                    Some
                                                      (Modalcell.prewhisker
                                                         (Suc
                                                            ( Suc (Zero, Triangle.modality),
                                                              Box.modality ))
                                                         (Suc
                                                            ( Suc (Zero, Triangle.modality),
                                                              Box.modality ))
                                                         cell tribox)
                                                | None -> None))
                                        | _ -> None)
                                    | Neq -> (
                                        (* n is a pure later-run laterᵇ *)
                                        let n' = Modality.Path (Suc (n_rest, ng), typ) in
                                        match later_run_bridge m' n' with
                                        | Some cell -> Some (Modalcell.vcomp cell to_later)
                                        | None -> None))
                                | Path (Zero, _) -> (
                                    match later_run_bridge m' (Modality.id typ) with
                                    | Some cell -> Some (Modalcell.vcomp cell to_later)
                                    | None -> None)))
                        | _ -> None)
                    | Neq -> (
                        (* m is a pure later-run laterᵃ (a≥1); its leading generator must be later *)
                        match Modality.Gen.compare mg Later.modality with
                        | Neq -> None
                        | Eq -> (
                            let m' = m in
                            match n with
                            | Path (Suc (_, ng), _) as np -> (
                                match Modality.Gen.compare ng Box.modality with
                                | Eq -> None (* laterᵃ ⇒ tribox·laterᵇ: no such cell *)
                                | Neq -> later_run_bridge m' np)
                            | Path (Zero, _) -> None))))
            | Path (Zero, _) -> (
                (* m = id_Timed, a pure later-run with a=0 *)
                match n with
                | Path (Suc (_, ng), _) as np -> (
                    match Modality.Gen.compare ng Box.modality with
                    | Eq -> None
                    | Neq -> later_run_bridge (Modality.id typ) np)
                | Path (Zero, _) -> None)))

  (* Every composite modality is isomorphic to a normal form.  find_unique normalizes both
     modalities, looks up the bridge 2-cell between the normal forms, and composes with the
     isomorphisms. *)
  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let (Normalize (_, xto, _)) = normalize x in
    let (Normalize (_, _, yfrom)) = normalize y in
    match bridge (Modalcell.vtgt xto) (Modalcell.vsrc yfrom) with
    | Some b -> Some (Modalcell.vcomp (Modalcell.vcomp yfrom b) xto)
    | None -> None

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "guarded"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun m ->
    "cell_"
    ^ string_of_int (Modality.length (Modalcell.vsrc m))
    ^ "_"
    ^ string_of_int (Modality.length (Modalcell.vtgt m))

  (* The theory of modality properties is nested inside the cells module, so that installing both
     theories instantiates this functor -- and in particular Modalcell.generate, which allocates
     fresh generating 2-cells -- only once. *)
  module Modalities : Modality.Theory = struct
    let tangible _ = true

    (* Every modality that normalizes to △ (with no laters) is transparent. *)
    let rec transparent_normal : type a m b. (a, m, b) Modality.t -> bool = function
      | Path (Zero, _) -> true
      | Path (Suc (m, g), mode) -> (
          match Modality.Gen.compare g Triangle.modality with
          | Eq -> true
          | Neq -> (
              match Modality.Gen.compare g Later.modality with
              | Eq -> transparent_normal (Path (m, mode))
              | Neq -> false))

    let transparent m =
      let (Normalize (m, _, _)) = normalize m in
      transparent_normal m

    let translucent _ = true
    let pellucid _ = false
  end
end

let install modes modalities modalcells =
  (match modalcells with
  | [] -> ()
  | _ -> failwith "wrong number of modal cell names for guarded mode theory");
  (match modes with
  | [ disc; ty ] ->
      TypeGen.name := disc;
      TimedGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for guarded mode theory");
  let module Type = Mode.Generate (TypeGen) in
  let module Timed = Mode.Generate (TimedGen) in
  let module Triangle = TriangleGen (Type) (Timed) in
  let module Box = BoxGen (Type) (Timed) in
  let module Later = LaterGen (Timed) in
  (match modalities with
  | [ tri; box; later ] ->
      Triangle.name := tri;
      Box.name := box;
      Later.name := later
  | [] -> ()
  | _ -> failwith "wrong number of modality names for guarded mode theory");
  Modality.set_one_char true modalities;
  let module Triangle = Modality.Generate (Triangle) in
  let module Box = Modality.Generate (Box) in
  let module Later = Modality.Generate (Later) in
  let module Cells = GuardedCells (Type) (Timed) (Triangle) (Box) (Later) in
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
