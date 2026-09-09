open Dim

(* An "ambiflection" has two modes, Disc and Type, and two generating modalities:

     △ : Disc → Type
     □ : Type → Disc

   with BOTH possible adjunctions between them: △ ⊣ □ and □ ⊣ △.  Thus each of △ and □ is
   simultaneously a "reflection" (a left adjoint) and a "coreflection" (a right adjoint), unlike in
   Adjunction, Local, Tconn, or Gwpt, where only one direction is ever postulated for a given
   generator.

   The composite □∘△ (an endomorphism of Disc) is genuinely invertible: the unit id_Disc ⇒ □△ of
   △ ⊣ □ and the counit □△ ⇒ id_Disc of □ ⊣ △ are declared mutually inverse, so □△ ≅ id_Disc
   exactly as in Local, Tconn, and Gwpt.

   The composite △∘□ (an endomorphism of Type), however, is only a *retract* of the identity, not
   an isomorphism -- exactly as for ♮ in Ambiflector, of which △∘□ here is the two-mode analogue.
   The counit △□ ⇒ id_Type of △ ⊣ □ and the unit id_Type ⇒ △□ of □ ⊣ △ compose (counit then unit)
   to the identity on △□ (so △□ is a retract of id_Type, split by the counit and unit); but
   composing the other way (unit then counit), id_Type ⇒ △□ ⇒ id_Type, is *not* the identity: it is
   a new, distinguished endomorphism of the identity modality, "zero", just as in Ambiflector.

   Consequently every hom-set of 2-cells is thin (has at most one element) except the
   endomorphisms of the identity modality at Type, which has exactly the two elements {id, zero};
   the sub-theory of 2-cells whose source and target modes are both Type is thus identical to the
   whole of Ambiflector, with △□ playing the role of ♮.  Modalities have exactly five normal forms:
   id_Disc, id_Type, △, □, and △□ (every longer alternating word collapses via the □△ ≅ id_Disc
   isomorphism, one adjacent pair at a time, down to one of these).

   Just as ♮ is adjoint to itself in Ambiflector, △□ is adjoint to itself here: composing the
   unit id_Type ⇒ △□ with △□ whiskered onto it gives a unit id_Type ⇒ △□∘△□, and composing △□
   whiskered onto the counit △□ ⇒ id_Type with the counit again gives a counit △□∘△□ ⇒ id_Type;
   the triangle identities hold automatically because the endomorphisms of △□ are also thin (so
   any two parallel self-maps of △□ are equal).  Thus △□ is sinister and, like the identity, △,
   and □, transparent. *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "ambiflection"
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete ambiflection"
end

module DiscGen (V : Variant) = struct
  let name = ref "Disc"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module TypeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module TriangleGen
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Disc.t
  type tgt = Type.t

  let src = Disc.mode
  let tgt = Type.mode
  let name = ref "△"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module BoxGen
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen) =
struct
  type src = Type.t
  type tgt = Disc.t

  let src = Type.mode
  let tgt = Disc.mode
  let name = ref "□"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module AmbiflectionCells
    (V : Variant)
    (Disc : Mode.Generated with module G := DiscGen(V))
    (Type : Mode.Generated with module G := TypeGen)
    (Triangle : Modality.Generated with module G := TriangleGen(V)(Disc)(Type))
    (Box : Modality.Generated with module G := BoxGen(V)(Disc)(Type)) =
struct
  let disc = Disc.mode
  let typ = Type.mode

  (* The two generating modalities. *)
  let tri = Modality.of_gen Triangle.modality
  let box = Modality.of_gen Box.modality

  (* The two-generator composite modalities: tribox = △∘□ (Type → Type) and boxtri = □∘△
     (Disc → Disc). *)
  let tribox = Modality.Path (Suc (Suc (Zero, Triangle.modality), Box.modality), typ)
  let boxtri = Modality.Path (Suc (Suc (Zero, Box.modality), Triangle.modality), disc)

  (* The generating 2-cells (source ⇒ target).  box_unit and box_unit_inv are mutually inverse,
     exhibiting □△ ≅ id_Disc: box_unit is the unit of △ ⊣ □, and box_unit_inv is the counit of
     □ ⊣ △.  unit and counit are NOT mutually inverse: unit is the unit of □ ⊣ △ and counit is the
     counit of △ ⊣ □; composing them one way (counit then unit) gives the identity on △□, but the
     other way (unit then counit) gives the distinguished nonidentity endomorphism "zero" of
     id_Type, which we give its own name since it's the one the user will need to refer to
     explicitly. *)
  let box_unit = Modalcell.of_gen (Modalcell.generate "η□△" (Modality.id disc) boxtri)
  let box_unit_inv = Modalcell.of_gen (Modalcell.generate "η□△⁻¹" boxtri (Modality.id disc))
  let unit = Modalcell.of_gen (Modalcell.generate "η" (Modality.id typ) tribox)
  let counit = Modalcell.of_gen (Modalcell.generate "ε" tribox (Modality.id typ))
  let zero = Modalcell.of_gen (Modalcell.generate "ø" (Modality.id typ) (Modality.id typ))

  (* △□ is also adjoint to itself, exactly as ♮ is in Ambiflector.  We build the two cells
     id_Type ⇒ △□∘△□ and △□∘△□ ⇒ id_Type needed for this by whiskering the ordinary unit/counit
     with △□ itself (postwhisker "m∘-" by △□, using Modality.comp to compute the resulting
     composite shape automatically) and then composing with the ordinary unit/counit again,
     exactly as mult/comult would be used in Ambiflector if △□ were a separate generator instead
     of a composite. *)
  let tribox_insert =
    Modalcell.postwhisker Zero (Suc (Suc (Zero, Triangle.modality), Box.modality)) tribox unit
  (* tribox_insert : △□ ⇒ △□∘△□ *)

  let tribox_extract =
    Modalcell.postwhisker (Suc (Suc (Zero, Triangle.modality), Box.modality)) Zero tribox counit
  (* tribox_extract : △□∘△□ ⇒ △□ *)

  let self_unit = Modalcell.vcomp tribox_insert unit
  let self_counit = Modalcell.vcomp counit tribox_extract

  (* A modality is sinister (a declared left adjoint) if it is an identity, △ (left adjoint to □,
     via △ ⊣ □), □ (left adjoint to △, via □ ⊣ △), or △□ (left adjoint to itself). *)
  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match
      ( Modality.compare_id f,
        Modality.compare f tri,
        Modality.compare f box,
        Modality.compare f tribox )
    with
    | Eq, _, _, _ -> Some (Modalcell.id_sinister (Modality.src f))
    | _, Eq, _, _ ->
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
                  counit;
                }))
    | _, _, Eq, _ ->
        (* □ ⊣ △ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = box;
                  right = tri;
                  right_left = Suc (Zero, Box.modality);
                  unit;
                  left_right = Suc (Zero, Triangle.modality);
                  counit = box_unit_inv;
                }))
    | _, _, _, Eq ->
        (* △□ ⊣ △□ *)
        Some
          (Sinister
             (Adjunction
                {
                  left = tribox;
                  right = tribox;
                  right_left = Suc (Suc (Zero, Triangle.modality), Box.modality);
                  unit = self_unit;
                  left_right = Suc (Suc (Zero, Triangle.modality), Box.modality);
                  counit = self_counit;
                }))
    | _ -> None

  let rec contains_gen : type a m n b. (a, m, n, b) Modalcell.t -> bool = function
    | Modalcell.Gen _ -> true
    | Modalcell.Id _ -> false
    | Modalcell.Hcomp (_, _, f, g) -> contains_gen f || contains_gen g
    | Modalcell.Vcomp (f, g) -> contains_gen f || contains_gen g

  (* Every hom-set is thin except the endomorphisms of the identity modality at Type, which has
     the two elements {id, zero}; those are distinguished by whether the cell's expression
     contains a generator (zero, whether used directly or built from unit and counit, always
     does; the identity never does). *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun c1 c2 ->
    match
      ( Modality.compare_id (Modalcell.vsrc c1),
        Modality.compare_id (Modalcell.vtgt c1),
        Mode.compare (Modalcell.hsrc c1) typ )
    with
    | Eq, Eq, Eq -> Bool.equal (contains_gen c1) (contains_gen c2)
    | _ -> true

  (* The normal forms of modalities are id_Disc, id_Type, △, □, and △□: every longer alternating
     word collapses, one adjacent □∘△ pair at a time, via the □△ ≅ id_Disc isomorphism. *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  (* Prepend a generator g (on the source side, i.e. applied first) to an already-normalized
     modality nf, and renormalize.  The only reduction is □∘△ ≅ id_Disc, which fires when g = △ is
     prepended to a normal form nf beginning (source-most) with □ -- i.e. nf = □ or nf = △□.  We
     are given the isomorphisms g_to : g·rest ⇒ g·nf and g_from : g·nf ⇒ g·rest obtained by
     prewhiskering the sub-isomorphisms by g, and we postcompose the reduction cell between g·nf
     and its normal form. *)
  let prepend : type c gg a nf b gm.
      (c, gg, a) Modality.Gen.t ->
      (a, nf, b) Modality.t ->
      (c, gm, (nf, gg) Modality.suc, b) Modalcell.t ->
      (c, (nf, gg) Modality.suc, gm, b) Modalcell.t ->
      (c, gm, b) normalize =
   fun g nf g_to g_from ->
    match nf with
    | Path (Zero, _) -> Normalize (Modality.suc nf g, g_to, g_from)
    | Path (Suc (inner, h), nb) -> (
        let rest = Modality.Path (inner, nb) in
        match (Modality.Gen.compare g Triangle.modality, Modality.Gen.compare h Box.modality) with
        | Eq, Eq ->
            (* □∘△ ≅ id_Disc *)
            let kill =
              Modalcell.hcomp
                (Suc (Suc (Zero, Box.modality), Triangle.modality))
                Zero (Modalcell.id rest) box_unit_inv in
            let unkill =
              Modalcell.hcomp Zero
                (Suc (Suc (Zero, Box.modality), Triangle.modality))
                (Modalcell.id rest) box_unit in
            Normalize (rest, Modalcell.vcomp kill g_to, Modalcell.vcomp g_from unkill)
        | _ -> Normalize (Modality.suc nf g, g_to, g_from))

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

  (* The unique 2-cell between two *normal-form* modalities, if one exists.  Since each of the
     four mode-pairs (Disc,Disc), (Disc,Type), (Type,Disc) has only a single normal form (id_Disc,
     △, and □ respectively), the only pair with more than one normal form is (Type,Type), with
     {id_Type, △□}; the nonidentity 2-cells between those are exactly unit and counit (the "zero"
     endomorphism of id_Type is never inserted automatically, only accessible via its own name). *)
  let bridge : type a p q b.
      (a, p, b) Modality.t -> (a, q, b) Modality.t -> (a, p, q, b) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match Modality.compare m (Modality.id typ) with
        | Eq -> (
            match Modality.compare n tribox with
            | Eq -> Some unit
            | Neq -> None)
        | Neq -> (
            match Modality.compare m tribox with
            | Eq -> (
                match Modality.compare n (Modality.id typ) with
                | Eq -> Some counit
                | Neq -> None)
            | Neq -> None))

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    let (Normalize (_, xto, _)) = normalize x in
    let (Normalize (_, _, yfrom)) = normalize y in
    match bridge (Modalcell.vtgt xto) (Modalcell.vsrc yfrom) with
    | Some b -> Some (Modalcell.vcomp (Modalcell.vcomp yfrom b) xto)
    | None -> None

  (* As in Ambiflector, △□ does not become usable to strip external parametricity: there is no
     parametric locker, and -external is not allowed with this theory. *)
  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "ambiflection"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun c ->
    match
      ( Modality.compare_id (Modalcell.vsrc c),
        Modality.compare_id (Modalcell.vtgt c),
        Mode.compare (Modalcell.hsrc c) typ )
    with
    | Eq, Eq, Eq -> if contains_gen c then "zero" else "id"
    | _ ->
        "cell_"
        ^ string_of_int (Modality.length (Modalcell.vsrc c))
        ^ "_"
        ^ string_of_int (Modality.length (Modalcell.vtgt c))

  (* The theory of modality properties is nested inside the cells module, so that installing both
     theories instantiates this functor -- and in particular Modalcell.generate, which allocates
     fresh generating 2-cells -- only once. *)
  module Modalities : Modality.Theory = struct
    let tangible _ = true
    let pellucid _ = false

    (* Every modality here (id_Disc, id_Type, △, □, or △□, its only five normal forms) is a left
       adjoint: △ and □ are each sinister via one of the two adjunctions, and every normal form is
       a composite of these (or an identity). *)
    let transparent _ = true
    let translucent _ = true
  end
end

let install (module V : Variant) modes modalities modalcells =
  let module Disc = DiscGen (V) in
  (match modes with
  | [ disc; ty ] ->
      Disc.name := disc;
      TypeGen.name := ty
  | [] -> ()
  | _ -> failwith ("wrong number of mode names for " ^ V.name ^ " mode theory"));
  let module Disc = Mode.Generate (Disc) in
  let module Type = Mode.Generate (TypeGen) in
  let module Tri = TriangleGen (V) (Disc) (Type) in
  let module Bx = BoxGen (V) (Disc) (Type) in
  (match modalities with
  | [ tri; box ] ->
      Tri.name := tri;
      Bx.name := box
  | [] -> ()
  | _ -> failwith ("wrong number of modality names for " ^ V.name ^ " mode theory"));
  Modality.set_one_char true modalities;
  let module Triangle = Modality.Generate (Tri) in
  let module Box = Modality.Generate (Bx) in
  let module Cells = AmbiflectionCells (V) (Disc) (Type) (Triangle) (Box) in
  (* The invertible unit η□△ and its inverse never need to be named; the non-invertible adjunction cells η△□, ε△□ and the zero cell ø do. *)
  (match modalcells with
  | [] -> ()
  | [ eta; eps; zero ] ->
      Modalcell.rename Cells.unit eta;
      Modalcell.rename Cells.counit eps;
      Modalcell.rename Cells.zero zero
  | _ -> failwith ("wrong number of modal cell names for " ^ V.name ^ " mode theory"));
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
