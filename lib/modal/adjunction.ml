open Dim
open Pairing

(* The "walking adjunction" has two modes, Disc and Type, and two generating modalities:

     △ : Disc → Type
     □ : Type → Disc

   with a single adjunction △ ⊣ □ and nothing else: the unit η : 1_Disc ⇒ □△ and counit ε : △□ ⇒ 1_Type satisfy the triangle identities, but neither is invertible.  Thus, unlike mode theories such as Spatial and Local, there is no "normalization" of modalities: no composite reduces, so (since sources and targets must match up) the modalities are exactly the alternating words in △ and □, none of which are isomorphic.

   The theory is also not locally posetal: parallel 2-cells can differ.  By the Schanuel-Street description of the free adjunction, a 2-cell between two words is uniquely determined by the "pairing" it induces on the generators occurring in its domain and codomain words: every generator is paired with exactly one other generator, either in the other word (a strand passing straight through, connecting two copies of the same generator) or in the same word (a strand that turns back).  An identity 2-cell pairs its domain with its codomain one-for-one; a counit pairs the △ and the □ in its domain; a unit pairs the □ and the △ in its codomain; horizontal composition takes disjoint unions of pairings; and vertical composition "follows the strings" through the middle word, "pulling zigzags straight" until it reaches either the new source or the new target word.  Two parallel 2-cells are equal exactly when they induce the same pairing.

   Concretely, listing the generators of each word in application order (first-applied first), the pairings arising from 2-cells m ⇒ n are exactly the following: some disjoint collection of *adjacent* pairs (□, △) in m are paired with each other (killed by counits), some disjoint collection of adjacent pairs (△, □) in n are paired with each other (created by units), and the remaining generators of m and n, which must form equal words, are paired with each other in order.  (Arcs connecting non-adjacent generators cannot occur: an arc can enclose no through-strands, by planarity, so the innermost arc under any arc would have to connect adjacent generators; but since the words alternate, the generators directly inside a domain arc (□, △) begin with △ and those directly inside a codomain arc (△, □) begin with □, so no arc can sit immediately inside another.  For the same reason, no closed loops can be created when composing pairings vertically: the source-most middle generator on such a loop would have to begin both a domain arc, as a □, and a codomain arc, as a △.) *)

module DiscGen = struct
  let name = ref "Disc"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TypeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TriangleGen
    (Disc : Mode.Generated with module G := DiscGen)
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Disc.t
  type tgt = Type.t

  let src = Disc.mode
  let tgt = Type.mode
  let name = ref "△"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module BoxGen
    (Disc : Mode.Generated with module G := DiscGen)
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Type.t
  type tgt = Disc.t

  let src = Type.mode
  let tgt = Disc.mode
  let name = ref "□"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module AdjunctionCells
    (Disc : Mode.Generated with module G := DiscGen)
    (Type : Mode.Generated with module G := TypeGen)
    (Triangle : Modality.Generated with module G := TriangleGen(Disc)(Type))
    (Box : Modality.Generated with module G := BoxGen(Disc)(Type)) =
struct
  let disc = Disc.mode
  let typ = Type.mode

  (* The two generating modalities. *)
  let tri = Modality.of_gen Triangle.modality
  let box = Modality.of_gen Box.modality

  (* The two-generator composite modalities: tribox = △∘□ (Type → Type) and boxtri = □∘△ (Disc → Disc). *)
  let tribox = Modality.Path (Suc (Suc (Zero, Triangle.modality), Box.modality), typ)
  let boxtri = Modality.Path (Suc (Suc (Zero, Box.modality), Triangle.modality), disc)

  (* The generating 2-cells: unit : 1_Disc ⇒ □△ and counit : △□ ⇒ 1_Type. *)
  let unit_gen = Modalcell.generate (Modality.id disc) boxtri
  let counit_gen = Modalcell.generate tribox (Modality.id typ)
  let unit = Modalcell.of_gen unit_gen
  let counit = Modalcell.of_gen counit_gen

  let gen_pairs : type a m n b. (a, m, n, b) Modalcell.Gen.t -> (endpoint * endpoint) list =
   fun g ->
    match Modalcell.Gen.compare g unit_gen with
    | Eq -> [ (Cod 0, Cod 1) ]
    | Neq -> (
        match Modalcell.Gen.compare g counit_gen with
        | Eq -> [ (Dom 0, Dom 1) ]
        | Neq -> failwith "unrecognized generating 2-cell in adjunction mode theory")

  let pairing c = Pairing.of_pairs (Pairing.of_cell ~allow_loops:false { gen_pairs } c)

  (* Two parallel 2-cells are equal exactly when they induce the same pairing. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun c1 c2 -> Pairing.equal (pairing c1) (pairing c2)

  (* A modality is sinister (a declared left adjoint) if it is an identity or △ (left adjoint to □).  These are the only left adjoints: any longer word contains a □, which has no right adjoint. *)
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
                  unit;
                  left_right = Suc (Zero, Box.modality);
                  counit;
                }))
    | _ -> None

  (* Count the 2-cells m ⇒ n, cutting off at two, and construct the cell if there is exactly one. *)
  type (_, _, _, _) count =
    | Zero_cells : ('a, 'm, 'n, 'b) count
    | One_cell : ('a, 'm, 'n, 'b) Modalcell.t -> ('a, 'm, 'n, 'b) count
    | Many_cells : ('a, 'm, 'n, 'b) count

  let add_count : type a m n b. (a, m, n, b) count -> (a, m, n, b) count -> (a, m, n, b) count =
   fun x y ->
    match (x, y) with
    | Zero_cells, y -> y
    | x, Zero_cells -> x
    | _ -> Many_cells

  (* The enumeration recurses on the source (first-applied) ends of the two words, following the combinatorial description of pairings given at the top of the file.  Each pairing is counted exactly once, by case analysis on the fate of the source-most generator of m. *)
  let rec count : type a m n b. (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) count =
   fun m n ->
    (* First alternative: the source-most generator of m is killed by a counit.  It can only be paired with the generator adjacent to it, so m must begin (in application order) with (□, △), i.e. m = m'' ∘ △□; and the cell factors as a counit at the source end of m followed by a cell m'' ⇒ n. *)
    let kills : (a, m, n, b) count =
      match m with
      | Path (Suc (Suc (ev, g2), g1), mb) -> (
          match
            (Modality.Gen.compare g1 Box.modality, Modality.Gen.compare g2 Triangle.modality)
          with
          | Eq, Eq -> (
              let m'' = Modality.Path (ev, mb) in
              match count m'' n with
              | Zero_cells -> Zero_cells
              | Many_cells -> Many_cells
              | One_cell c ->
                  let kill =
                    Modalcell.hcomp
                      (Suc (Suc (Zero, Triangle.modality), Box.modality))
                      Zero (Modalcell.id m'') counit in
                  One_cell (Modalcell.vcomp c kill))
          | _ -> Zero_cells)
      | _ -> Zero_cells in
    (* Second alternative: the source-most generator of m (if any) passes straight through to n.  Then all the generators of n on the source side of its partner must be paired among themselves, forming unit-created adjacent (△, □) pairs tiling the source end of n.  So we strip zero or more such pairs from n, and then either pair up the source-most generators of m and the stripped n and recurse, or finish if both are empty.  The wrap argument turns a cell targeting the stripped n back into one targeting n, by vertically composing with the unit cells that create the stripped pairs. *)
    let rec strip : type nk.
        (a, nk, b) Modality.t ->
        ((a, m, nk, b) Modalcell.t -> (a, m, n, b) Modalcell.t) ->
        (a, m, n, b) count =
     fun nk wrap ->
      let here : (a, m, n, b) count =
        match (m, nk) with
        | Path (Zero, _), Path (Zero, _) -> One_cell (wrap (Modalcell.id m))
        | Path (Suc (mev, g), mb), Path (Suc (nev, h), nb) -> (
            match Modality.Gen.compare g h with
            | Eq -> (
                match count (Modality.Path (mev, mb)) (Modality.Path (nev, nb)) with
                | Zero_cells -> Zero_cells
                | Many_cells -> Many_cells
                | One_cell c ->
                    One_cell
                      (wrap
                         (Modalcell.hcomp
                            (Suc (Zero, g))
                            (Suc (Zero, g))
                            c
                            (Modalcell.id (Modality.of_gen g)))))
            | Neq -> Zero_cells)
        | _ -> Zero_cells in
      let deeper : (a, m, n, b) count =
        match nk with
        | Path (Suc (Suc (nev, g2), g1), nb) -> (
            match
              (Modality.Gen.compare g1 Triangle.modality, Modality.Gen.compare g2 Box.modality)
            with
            | Eq, Eq ->
                let n1 = Modality.Path (nev, nb) in
                let create =
                  Modalcell.hcomp Zero
                    (Suc (Suc (Zero, Box.modality), Triangle.modality))
                    (Modalcell.id n1) unit in
                strip n1 (fun c -> wrap (Modalcell.vcomp create c))
            | _ -> Zero_cells)
        | _ -> Zero_cells in
      add_count here deeper in
    add_count kills (strip n (fun c -> c))

  (* A 2-cell can be inserted as an implicit key only when it is unique; if there are several parallel cells, the user must disambiguate. *)
  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match count x y with
    | One_cell c -> Some c
    | Zero_cells | Many_cells -> None

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "adjunction"

  (* Since parallel 2-cells can differ, we display a cell by its pairing. *)
  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun c -> Pairing.to_string (Pairing.of_cell ~allow_loops:false { gen_pairs } c)
end

module AdjunctionModalities
    (Disc : Mode.Generated with module G := DiscGen)
    (Type : Mode.Generated with module G := TypeGen)
    (Triangle : Modality.Generated with module G := TriangleGen(Disc)(Type))
    (Box : Modality.Generated with module G := BoxGen(Disc)(Type)) : Modality.Theory = struct
  let tangible _ = true
  let pellucid _ = false

  (* The left adjoints (the identities and △) are transparent. *)
  let rec transparent : type a m b. (a, m, b) Modality.t -> bool = function
    | Path (Zero, _) -> true
    | Path (Suc (m, g), mode) -> (
        match Modality.Gen.compare g Box.modality with
        | Eq -> false
        | Neq -> transparent (Path (m, mode)))

  let translucent _ = true
end

let install modes modalities =
  (match modes with
  | [ disc; ty ] ->
      DiscGen.name := disc;
      TypeGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for adjunction mode theory");
  let module Disc = Mode.Generate (DiscGen) in
  let module Type = Mode.Generate (TypeGen) in
  let module Tri = TriangleGen (Disc) (Type) in
  let module Bx = BoxGen (Disc) (Type) in
  (match modalities with
  | [ tri; box ] ->
      Tri.name := tri;
      Bx.name := box
  | [] -> ()
  | _ -> failwith "wrong number of modality names for adjunction mode theory");
  Modality.set_one_char true modalities;
  let module Triangle = Modality.Generate (Tri) in
  let module Box = Modality.Generate (Bx) in
  Modalcell.choose_theory (module AdjunctionCells (Disc) (Type) (Triangle) (Box) : Modalcell.Theory);
  Modality.choose_theory
    (module AdjunctionModalities (Disc) (Type) (Triangle) (Box) : Modality.Theory)
