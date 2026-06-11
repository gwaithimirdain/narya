open Util
open Tbwd

(* We define "dimensions" to be type-level natural numbers.  However, in the interface we expose only that they are a type-level monoid with some extra structure.  Thus, the implementation is parametric over a specification of dimensions and their operators.  *)

(* Moreover, instead of using the literal natural numbers N, we use the isomorphic type Word(Unit).  In the future we will generalize this to words over multiple directions of parametricity. *)

include Word.Make (Unitcomparable)

(* Re-export the generator module so consumers can refer to ['g D.G.t] rather than naming Unitcomparable directly.  When generators eventually become multi-direction, only this alias changes. *)
module G = Unitcomparable

(* The unique generator witness for the (currently single-generator) dimension theory.  To prepare for future multi-generator generalization, consumers should refer to this rather than writing the constructor [Unit] directly. *)
let deg : unit G.t = G.Unit

(* Type-level natural numbers are represented by words over Unit, which are isomorphic to natural numbers.  The two-argument [suc] is inherited from Word; we only expose alias [one] and [two] for ergonomics in code that talks about specific small dimensions. *)
type one = (zero, unit) suc
type two = (one, unit) suc

let one : one t = suc zero deg
let two : two t = suc one deg

type ('a, 'g, 'b) insert = ('a, 'g, 'b) Tbwd.insert

(* The commutativity-dependent operations plus_suc, suc_plus, and suc_plus_eq_suc that this file once provided have been removed entirely: the cube/tube/icube/pbijmap data structures are now indexed so that all their bookkeeping is word associativity (see cube.ml), and the structured generator-generic versions live in Word. *)

(* Integer hackery, for converting from strings to degeneracies.  Should be replaced by something like a Bwv parametrized by a word, perhaps a version of a Tuple. *)

let rec of_int : int -> wrapped =
 fun n ->
  if n <= 0 then Wrap zero
  else
    let (Wrap w) = of_int (n - 1) in
    Wrap (suc w deg)

(* An insert-of-int is just an [insert_into], i.e. an insertion into some prefix at some position, producing the given word. *)
type 'b insert_of_int = 'b insert_into

let insert_of_int : type bsuc. bsuc t -> int -> bsuc insert_of_int option =
 fun n x ->
  if x < 0 then None
  else
    let rec drop : type a. int -> a Seq.t -> a Seq.t =
     fun k s ->
      if k <= 0 then s
      else
        match s () with
        | Seq.Nil -> s
        | Seq.Cons (_, t) -> drop (k - 1) t in
    match drop x (all_inserts n) () with
    | Seq.Nil -> None
    | Seq.Cons (i, _) -> Some i

(* Trichotomy.  With multiple generators, two words need not be comparable, so there is a fourth case. *)

type (_, _) trichotomy =
  | Eq : ('n, 'n) trichotomy
  | Lt : ('m, ('n, 'g) suc, 'mn) plus -> ('m, 'mn) trichotomy
  | Gt : ('m, ('n, 'g) suc, 'mn) plus -> ('mn, 'm) trichotomy
  | Incomparable : ('m, 'n) trichotomy

let trichotomy : type m n. m t -> n t -> (m, n) trichotomy =
 fun m n ->
  match factor m n with
  | Some (Factor Zero) -> Eq
  | Some (Factor (Suc _ as k)) -> Gt k
  | _ -> (
      match factor n m with
      | Some (Factor Zero) -> Eq
      | Some (Factor (Suc _ as k)) -> Lt k
      | _ -> Incomparable)
