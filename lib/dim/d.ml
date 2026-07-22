open Util
open Tbwd

(* We define "dimensions" to be type-level natural numbers.  However, in the interface we expose only that they are a type-level monoid with some extra structure.  Thus, the implementation is parametric over a specification of dimensions and their operators.  *)

(* Moreover, instead of using the literal natural numbers N, we use the isomorphic type Word(Unit).  In the future we will generalize this to words over multiple directions of parametricity. *)

include Word.MakeDecidable (Unitcomparable)

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

(* Integer hackery, for converting from strings to degeneracies.  Should be replaced by something like a Bwv parametrized by a word, perhaps a version of a Tuple. *)

let rec of_int : int -> wrapped =
 fun n ->
  if n <= 0 then Wrap zero
  else
    let (Wrap w) = of_int (n - 1) in
    Wrap (suc w deg)

let insert_of_int : type bsuc. bsuc t -> int -> bsuc insert_into option =
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
