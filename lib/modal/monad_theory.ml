open Dim

(* We call this module "Monad_theory" so it doesn't conflict with Util.Monad. *)

(* A single mode Type with a single endomodality "sharp" equipped with a monad structure: a unit
   η : id ⇒ sharp and a multiplication μ : sharp∘sharp ⇒ sharp, satisfying the monad laws (unit
   laws and associativity) and nothing else -- in particular, sharp is *not* declared idempotent
   (there is no cell or isomorphism sharp ⇒ sharp∘sharp), so this is the free monad on a single
   endofunctor, dual to Comonad's free (non-idempotent) comonad. There is no discrete version:
   unlike a comonad's counit, a monad's unit gives no way to build a "locker" for negative types
   (that requires a *left* adjoint / sinister modality, and sharp is not declared sinister), so
   there is nothing for -discrete-monad to do differently.

   Consequently the theory is not locally posetal: parallel 2-cells can differ.  Since the only
   generator is sharp, every modality is just sharpⁿ for some n, and (dually to Comonad) a 2-cell
   sharpᵃ ⇒ sharpᵇ is uniquely determined by an ordered "composition" of a into b nonnegative parts
   l₁,...,l_b (the number of cells is C(a+b-1,b-1)): the j-th output receives lⱼ of the a inputs,
   merged via a canonically-associated chain of multiplications (or, if lⱼ = 0, created fresh via
   the unit), and the groups tile the inputs in order.  Two parallel cells are equal exactly when
   they induce the same sequence (l₁,...,l_b).

   Consequently there is a unique 2-cell sharpᵃ ⇒ sharpᵇ exactly when a=0 (the unique all-unit
   cell, any b, each output created fresh) or b=1 (the unique canonical a-fold multiplication,
   any a); when a≥1 and b=0 there is no such cell (a monad's unit creates but never deletes); and
   when a≥1 and b≥2 there are several, so find_unique correctly returns None in both cases
   (forcing the user to disambiguate, or reporting that no cell exists, respectively). *)

module TestmodeGen = struct
  let name = ref "Type"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module SharpGen (Testmode : Mode.Generated with module G := TestmodeGen) = struct
  type src = Testmode.t
  type tgt = Testmode.t

  let src = Testmode.mode
  let tgt = Testmode.mode
  let name = ref "♯"

  type nonparametric = D.zero

  let nonparametric = D.zero
end

module MonadCells
    (Testmode : Mode.Generated with module G := TestmodeGen)
    (Sharp : Modality.Generated with module G := SharpGen(Testmode)) =
struct
  let typ = Testmode.mode

  type sharp_shape = (Testmode.t Modality.id, Sharp.t) Modality.suc

  let sharp = Modality.of_gen Sharp.modality
  let sharpsharp = Modality.Path (Suc (Suc (Zero, Sharp.modality), Sharp.modality), typ)
  let unit_gen = Modalcell.generate "η" (Modality.id typ) sharp
  let mult_gen = Modalcell.generate "μ" sharpsharp sharp
  let unit = Modalcell.of_gen unit_gen
  let mult = Modalcell.of_gen mult_gen

  let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) Modalcell.sinister option = function
    | Path (Zero, mode) -> Some (Modalcell.id_sinister mode)
    | _ -> None

  (* The invariant of a 2-cell: the sequence (l₁,...,l_b), b=length of the codomain word,
     recording how many of the domain generators (in order) merge into each codomain generator. *)
  let rec signature : type a m n b. (a, m, n, b) Modalcell.t -> int list = function
    | Modalcell.Id m -> List.init (Modality.length m) (fun _ -> 1)
    | Modalcell.Gen g -> (
        match Modalcell.Gen.compare g unit_gen with
        | Eq -> [ 0 ]
        | Neq -> (
            match Modalcell.Gen.compare g mult_gen with
            | Eq -> [ 2 ]
            | Neq -> failwith "monad: unrecognized generating 2-cell"))
    | Modalcell.Hcomp (_, _, y, x) -> signature x @ signature y
    | Modalcell.Vcomp (y, x) ->
        (* Partition x's sequence into groups whose sizes are given by y's sequence, and sum each
           group, to get the composite's sequence. *)
        let rec partition xs ys =
          match xs with
          | [] -> []
          | k :: xs' ->
              let grp = List.filteri (fun i _ -> i < k) ys in
              let rest = List.filteri (fun i _ -> i >= k) ys in
              List.fold_left ( + ) 0 grp :: partition xs' rest in
        partition (signature y) (signature x)

  (* Two parallel 2-cells are equal exactly when they induce the same sequence. *)
  let compare : type a m n b. (a, m, n, b) Modalcell.t -> (a, m, n, b) Modalcell.t -> bool =
   fun c1 c2 -> signature c1 = signature c2

  (* The unique cell id ⇒ sharpᵇ, for any b, creating each output fresh with the unit. *)
  let rec chain_unit : type a n b. (a, n, b) Modality.t -> (a, a Modality.id, n, b) Modalcell.t =
   fun md ->
    match md with
    | Path (Zero, mode) -> Modalcell.id2 mode
    | Path (Suc (inner, g), mode) -> (
        match Modality.Gen.compare g Sharp.modality with
        | Neq -> failwith "monad: unrecognized generator"
        | Eq ->
            let rest = chain_unit (Modality.Path (inner, mode)) in
            Modalcell.hcomp Zero (Suc (Zero, g)) rest unit)

  (* The unique cell m ⇒ sharp, for any m = sharpᵃ, merging the a inputs into the single output
     via a canonically-associated chain of multiplications (the leading input is left alone and
     the rest is merged further, recursing on m's tail; associativity means any other association
     would give an equal, though not identical, cell). *)
  let rec chain_mult : type n.
      (Testmode.t, n, Testmode.t) Modality.t -> (Testmode.t, n, sharp_shape, Testmode.t) Modalcell.t
      =
   fun m ->
    match Modality.compare m sharp with
    | Eq -> Modalcell.id sharp
    | Neq -> (
        match m with
        | Path (Suc (inner, g), mode) -> (
            match Modality.Gen.compare g Sharp.modality with
            | Neq -> failwith "monad: unrecognized generator"
            | Eq ->
                let rest = chain_mult (Modality.Path (inner, mode)) in
                let step =
                  Modalcell.hcomp (Suc (Zero, g)) (Suc (Zero, g)) rest (Modalcell.id sharp) in
                Modalcell.vcomp mult step)
        | Path (Zero, _) -> failwith "monad: chain_mult called on identity")

  let find_unique : type a m n b.
      (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) Modalcell.t option =
   fun x y ->
    match x with
    | Path (Zero, _) -> (
        match y with
        | Path (Zero, _) -> Some (Modalcell.id x)
        | Path (Suc (_, _), _) -> Some (chain_unit y))
    | Path (Suc (_, _), _) -> (
        match y with
        | Path (Zero, _) -> None
        | Path (Suc (Zero, g), _) -> (
            match Modality.Gen.compare g Sharp.modality with
            | Neq -> None
            | Eq -> Some (chain_mult x))
        | Path (Suc (Suc (_, _), _), _) -> None)

  let parametric_locker : type a. a Mode.t -> (a Modalcell.parametric_locker, string) Result.t =
   fun _ -> Error "monad"

  (* Since parallel 2-cells can differ, we display a cell by its signature. *)
  let to_string : type a m n b. (a, m, n, b) Modalcell.t -> string =
   fun c -> "[" ^ String.concat "," (List.map string_of_int (signature c)) ^ "]"
end

let install modes modalities =
  (match modes with
  | [ ty ] -> TestmodeGen.name := ty
  | [] -> ()
  | _ -> failwith "wrong number of mode names for monad mode theory");
  let module Testmode = Mode.Generate (TestmodeGen) in
  let module Sharp = SharpGen (Testmode) in
  (match modalities with
  | [ sharp ] -> Sharp.name := sharp
  | [] -> ()
  | _ -> failwith "wrong number of modality names for monad mode theory");
  Modality.set_one_char true modalities;
  let module Sharp = Modality.Generate (Sharp) in
  Modalcell.choose_theory (module MonadCells (Testmode) (Sharp) : Modalcell.Theory)
