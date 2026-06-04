open Util
open Tbwd

(* We define "dimensions" to be type-level natural numbers.  However, in the interface we expose only that they are a type-level monoid with some extra structure.  Thus, the implementation is parametric over a specification of dimensions and their operators.  *)

(* Moreover, instead of using the literal natural numbers N, we use the isomorphic type Word(Unit).  In the future we will generalize this to words over multiple directions of parametricity. *)

include Word.Make (Unitcomparable)

(* The unique generator witness for the (currently single-generator) dimension theory.  To prepare for future multi-generator generalization, consumers should refer to this rather than writing the constructor [Unit] directly. *)
let deg : unit Unitcomparable.t = Unit

(* Type-level natural numbers are represented by words over Unit, which are isomorphic to natural numbers.  The two-argument [suc] is inherited from Word; we only expose alias [one] and [two] for ergonomics in code that talks about specific small dimensions. *)
type one = (zero, unit) suc
type two = (one, unit) suc

let one : one t = suc zero deg
let two : two t = suc one deg

type ('a, 'b) insert = ('a, unit, 'b) Tbwd.insert

(* TODO: temporary scaffolding.  These three functions are commutativity-dependent and will be removed once all call sites in cube/icube/tube/etc. are restructured to use Word.ml's structured forms (Phase 7). *)

let rec plus_suc : type m n p.
    ((m, unit) suc, n, p) plus -> (m, (n, unit) suc, p) plus = function
  | Zero -> Suc (Zero, Unit)
  | Suc (x, Unit) -> Suc (plus_suc x, Unit)

let rec suc_plus_eq_suc : type m n p.
    (m, n, p) plus -> ((m, unit) suc, n, (p, unit) suc) plus = function
  | Zero -> Zero
  | Suc (x, Unit) -> Suc (suc_plus_eq_suc x, Unit)

let suc_plus : type m n p.
    (m, (n, unit) suc, p) plus -> ((m, unit) suc, n, p) plus =
 fun x ->
  let (Suc (y, Unit)) = suc_plus_eq_suc x in
  y

(* Integer hackery, for converting from strings to degeneracies.  Should be replaced by something like a Bwv parametrized by a word, perhaps a version of a Tuple. *)

let rec of_int : int -> wrapped =
 fun n ->
  if n <= 0 then Wrap zero
  else
    let (Wrap w) = of_int (n - 1) in
    Wrap (suc w deg)

type _ insert_of_int =
  | Insert_of_int : ('b, ('b, unit) suc) insert -> ('b, unit) suc insert_of_int

let rec insert_of_int : type bsuc. bsuc t -> int -> bsuc insert_of_int option =
 fun n x ->
  match n with
  | Word Zero -> None
  | Word (Suc (n, Unit)) -> (
      if x < 0 then None
      else if x = 0 then Some (Insert_of_int Now)
      else
        match insert_of_int (Word n) (x - 1) with
        | None -> None
        | Some (Insert_of_int y) -> Some (Insert_of_int (Later y)))

(* Trichotomy.  Should be replaced by factoring/pushouts. *)

type (_, _) trichotomy =
  | Eq : ('n, 'n) trichotomy
  | Lt : ('m, ('n, unit) suc, 'mn) plus -> ('m, 'mn) trichotomy
  | Gt : ('m, ('n, unit) suc, 'mn) plus -> ('mn, 'm) trichotomy

let trichotomy : type m n. m t -> n t -> (m, n) trichotomy =
 fun m n ->
  match factor m n with
  | Some (Factor Zero) -> Eq
  | Some (Factor (Suc (_, Unit) as k)) -> Gt k
  | _ -> (
      match factor n m with
      | Some (Factor Zero) -> Eq
      | Some (Factor (Suc (_, Unit) as k)) -> Lt k
      | _ -> assert false)
