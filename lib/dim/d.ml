open Util
open Tbwd

(* We define "dimensions" to be type-level natural numbers.  However, in the interface we expose only that they are a type-level monoid with some extra structure.  Thus, the implementation is parametric over a specification of dimensions and their operators.  *)

(* Moreover, instead of using the literal natural numbers N, we use the isomorphic type Word(Unit).  In the future we will generalize this to words over multiple directions of parametricity. *)

module Unit = struct
  type 'a t = Unit : unit t

  let compare : type a b. a t -> b t -> (a, b) Eq.compare =
   fun a b ->
    match (a, b) with
    | Unit, Unit -> Eq
end

include Word.Make (Unit)

(* Type-level natural numbers are represented by words over Unit, which are isomorphic to natural numbers.  We expose a unary [suc] for compatibility with the rest of the dim library. *)
type 'n suc = ('n, unit) snoc
type one = zero suc
type two = one suc

let suc : type n. n t -> n suc t = fun n -> suc n Unit
let one : one t = suc zero
let two : two t = suc one

type ('a, 'b) insert = ('a, unit, 'b) Tbwd.insert

(* Properties of the successor that don't generalize to other words.  Functions that use these will need to be rewritten. *)

let rec plus_suc : type m n p. (m suc, n, p) plus -> (m, n suc, p) plus = function
  | Zero -> Suc (Zero, Unit)
  | Suc (x, Unit) -> Suc (plus_suc x, Unit)

let rec suc_plus_eq_suc : type m n p. (m, n, p) plus -> (m suc, n, p suc) plus = function
  | Zero -> Zero
  | Suc (x, Unit) -> Suc (suc_plus_eq_suc x, Unit)

let suc_plus : type m n p. (m, n suc, p) plus -> (m suc, n, p) plus =
 fun x ->
  let (Suc (y, Unit)) = suc_plus_eq_suc x in
  y

(* Integer hackery, for converting from strings to degeneracies.  Should be replaced by something like a Bwv parametrized by a word, perhaps a version of a Tuple. *)

let rec of_int : int -> wrapped =
 fun n ->
  if n <= 0 then Wrap zero
  else
    let (Wrap w) = of_int (n - 1) in
    Wrap (suc w)

type _ insert_of_int = Insert_of_int : ('b, 'b suc) insert -> 'b suc insert_of_int

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
  | Lt : ('m, 'n suc, 'mn) plus -> ('m, 'mn) trichotomy
  | Gt : ('m, 'n suc, 'mn) plus -> ('mn, 'm) trichotomy

let rec trichotomy : type m n. m t -> n t -> (m, n) trichotomy =
 fun m n ->
  match (m, n) with
  | Word Zero, Word Zero -> Eq
  | Word Zero, Word (Suc (_, Unit)) -> Lt (zero_plus n)
  | Word (Suc (_, Unit)), Word Zero -> Gt (zero_plus m)
  | Word (Suc (m', Unit)), Word (Suc (n', Unit)) -> (
      match trichotomy (Word m') (Word n') with
      | Eq -> Eq
      | Lt p -> Lt (suc_plus_eq_suc p)
      | Gt p -> Gt (suc_plus_eq_suc p))
