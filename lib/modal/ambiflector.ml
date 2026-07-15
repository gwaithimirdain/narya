open Dim

(* The "ambiflector" mode theory has one mode Type and one self-modality generator ♮ that is simultaneously a reflector (idempotent monad: unit id ⇒ ♮ and multiplication ♮∘♮ ⇒ ♮) and a coreflector (idempotent comonad: counit ♮ ⇒ id and comultiplication ♮ ⇒ ♮∘♮), with the multiplication and comultiplication postulated to be mutually inverse (so ♮∘♮ ≅ ♮, "idempotent up to isomorphism").

   Composing the unit and counit the two possible ways gives different results.  Applying the counit and then the unit, ♮ ⇒ id ⇒ ♮, is declared to be the identity on ♮: so ♮ is a retract of the identity modality, split by counit (inclusion) and unit (retraction).  But applying the unit and then the counit, id ⇒ ♮ ⇒ id, is *not* the identity on id: it is a new, distinguished endomorphism of the identity modality, "zero".  (Since ♮ is a retract of id, zero = counit∘unit is automatically idempotent, zero∘zero = zero, though it is not itself a generator -- it is just the named composite of unit and counit.)

   The theory is "almost" locally posetal: every hom-set of 2-cells is thin (has at most one element) except the endomorphisms of the identity modality, which has exactly the two elements {id, zero}.  Modalities still have just two normal forms, id and ♮, since every nonempty word in ♮ collapses to ♮ via the multiplication/comultiplication iso; and find_unique never actually needs to choose between id and zero, since it only ever inserts the trivial identity key when the source and target modalities already coincide, or the unit/counit when they don't.  But `compare` must still be able to distinguish id from zero on identity-typed cells, which it does by checking whether the cell's expression contains any occurrence of a generator: the identity never does, while zero, being built from unit and counit, always does.

   ♮ is also adjoint to itself, ♮ ⊣ ♮: composing the reflector unit id ⇒ ♮ with the comultiplication ♮ ⇒ ♮∘♮ gives a unit id ⇒ ♮∘♮, and composing the multiplication ♮∘♮ ⇒ ♮ with the coreflector counit ♮ ⇒ id gives a counit ♮∘♮ ⇒ id; the triangle identities hold automatically because the endomorphisms of ♮ are also thin (so any two parallel self-maps of ♮ are equal).  Thus ♮ is sinister and, like the identity, transparent.

   The discrete variant makes ♮ nonparametric.  There is no parametric locker (♮ does not become usable to strip external parametricity, unlike the discrete variants of some other mode theories), and -external is not allowed with it. *)

module type Variant = sig
  type nonparametric

  val nonparametric : nonparametric D.t
  val name : string
end

module Ordinary = struct
  type nonparametric = D.zero

  let nonparametric = D.zero
  let name = "ambiflector"
end

module Discrete = struct
  type nonparametric = D.one

  let nonparametric = D.one
  let name = "discrete ambiflector"
end

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module AmbGen (V : Variant) (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♮"

  type nonparametric = V.nonparametric

  let nonparametric = V.nonparametric
end

module AmbiflectorCells
    (V : Variant)
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Amb : Modality.Generated with module G := AmbGen(V)(Testmode)) =
struct
  let typ = Testmode.mode
  let amb = Modality.of_gen Amb.modality
  let ambamb = Modality.Path (Suc (Suc (Zero, Amb.modality), Amb.modality), typ)

  (* Reflector data: unit and multiplication. *)
  let unit = Modalcell.of_gen (Modalcell.generate "η" (Modality.id typ) amb)
  let mult = Modalcell.of_gen (Modalcell.generate "μ" ambamb amb)

  (* Coreflector data: counit and comultiplication. *)
  let counit = Modalcell.of_gen (Modalcell.generate "ε" amb (Modality.id typ))
  let comult = Modalcell.of_gen (Modalcell.generate "Δ" amb ambamb)

  (* ♮ is adjoint to itself: unit id ⇒ ♮∘♮ (unit followed by comult) and counit ♮∘♮ ⇒ id
     (mult followed by counit). *)
  let adj_unit = Modalcell.vcomp comult unit
  let adj_counit = Modalcell.vcomp counit mult

  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option =
   fun f ->
    match Modality.compare_id f with
    | Eq -> Some (Modalcell.id_sinister (Modality.src f))
    | Neq -> (
        match Modality.compare f amb with
        | Eq ->
            Some
              (Sinister
                 (Adjunction
                    {
                      left = amb;
                      right = amb;
                      right_left = Suc (Zero, Amb.modality);
                      unit = adj_unit;
                      left_right = Suc (Zero, Amb.modality);
                      counit = adj_counit;
                    }))
        | Neq -> None)

  let rec contains_gen : type a m n b. (a, m, n, b) Modalcell.t -> bool = function
    | Modalcell.Gen _ -> true
    | Modalcell.Id _ -> false
    | Modalcell.Hcomp (_, _, f, g) -> contains_gen f || contains_gen g
    | Modalcell.Vcomp (f, g) -> contains_gen f || contains_gen g

  (* Every hom-set is thin except the endomorphisms of the identity modality, which has
     the two elements {id, zero}; those are distinguished by whether the cell's
     expression contains a generator (zero, built from unit and counit, always does;
     the identity never does). *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun c1 c2 ->
    match (Modality.compare_id (Modalcell.vsrc c1), Modality.compare_id (Modalcell.vtgt c1)) with
    | Eq, Eq -> Bool.equal (contains_gen c1) (contains_gen c2)
    | _ -> true

  (* The normal forms of modalities are id and ♮: every nonempty word in ♮ is
     isomorphic to ♮ alone, via mult/comult. *)
  type (_, _, _) normalize =
    | Normalize :
        ('a, 'nf, 'b) Modality.t * ('a, 'm, 'nf, 'b) Modalcell.t * ('a, 'nf, 'm, 'b) Modalcell.t
        -> ('a, 'm, 'b) normalize

  let prepend : type c gg a nf b gm.
      (c, gg, a) Modality.Gen.t ->
      (a, nf, b) Modality.t ->
      (c, gm, (nf, gg) Modality.suc, b) Modalcell.t ->
      (c, (nf, gg) Modality.suc, gm, b) Modalcell.t ->
      (c, gm, b) normalize =
   fun g nf g_to g_from ->
    match Modality.Gen.compare g Amb.modality with
    | Neq -> failwith "ambiflector: unrecognized generator"
    | Eq -> (
        match Modality.compare nf (Modality.id typ) with
        | Eq -> Normalize (amb, g_to, g_from)
        | Neq -> (
            match Modality.compare nf amb with
            | Eq -> Normalize (amb, Modalcell.vcomp mult g_to, Modalcell.vcomp g_from comult)
            | Neq -> failwith "ambiflector: unrecognized modality composite in normalize"))

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

  let bridge : type a p q b.
      (a, p, b) Modality.t -> (a, q, b) Modality.t -> (a, p, q, b) Modalcell.t option =
   fun m n ->
    match Modality.compare m n with
    | Eq -> Some (Modalcell.id m)
    | Neq -> (
        match Modality.compare m (Modality.id typ) with
        | Eq -> (
            match Modality.compare n amb with
            | Eq -> Some unit
            | Neq -> None)
        | Neq -> (
            match Modality.compare m amb with
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

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "ambiflector"

  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun c ->
    match (Modality.compare_id (Modalcell.vsrc c), Modality.compare_id (Modalcell.vtgt c)) with
    | Eq, Eq -> if contains_gen c then "zero" else "id"
    | _ ->
        "cell_"
        ^ string_of_int (Modality.length (Modalcell.vsrc c))
        ^ "_"
        ^ string_of_int (Modality.length (Modalcell.vtgt c))

  (* The theory of modality properties is nested inside the cells module, so that installing
     both theories instantiates this functor -- and in particular Modalcell.generate, which
     allocates fresh generating 2-cells -- only once. *)
  module Modalities : Modality.Theory = struct
    let tangible _ = true
    let pellucid _ = false

    (* Every modality here (id or ♮, its only two normal forms) is a left adjoint, since ♮ is
       adjoint to itself. *)
    let transparent _ = true
    let translucent _ = true
  end
end

let install (module V : Variant) modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith ("wrong number of mode names for " ^ V.name ^ " mode theory"));
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Nat = AmbGen (V) (Testmode) in
  (match modalities with
  | [ amb ] -> Nat.name := amb
  | [] -> ()
  | _ -> failwith ("wrong number of modality names for " ^ V.name ^ " mode theory"));
  Modality.set_one_char true modalities;
  let module Amb = Modality.Generate (Nat) in
  let module Cells = AmbiflectorCells (V) (Testmode) (Amb) in
  Modalcell.choose_theory (module Cells : Modalcell.Theory);
  Modality.choose_theory (module Cells.Modalities : Modality.Theory)
