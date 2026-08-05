open Util

(* We define "dimensions" to be type-level natural numbers.  However, in the interface we expose only that they are a type-level monoid with some extra structure.  Thus, the implementation is parametric over a specification of dimensions and their operators.  *)

(* Moreover, instead of using the literal natural numbers N, we use the isomorphic type Word(Unit).  In the future we will generalize this to words over multiple directions of parametricity. *)

module G = struct
  include Unitcomparable

  type ('a, 'b) commute = unit
  type 'a central = unit

  let commute_inv : type a b. a t -> b t -> (a, b) commute -> (b, a) commute = fun _ _ () -> ()
  let commute : type a b. a t -> b t -> (a, b) commute option = fun _ _ -> Some ()
  let central_commute : type a b. a t -> b t -> a central -> (a, b) commute = fun _ _ () -> ()
end

include Word.MakeDecidable (G)

(* TEMPORARY.  At present there is only one generator, and all generators have been declared to commute, so witnesses of commutation can be produced out of thin air.  The following functions do that.  Each use of them marks a place where the machinery of insertions and permutations demands a symmetry that we currently get for free; when commutation is weakened, these functions will go away and every use will have to be replaced by an actual witness (or the algorithm restructured to do without it). *)

let free_commute : type g h. (g, h) G.commute = ()

(* Similarly, every generator is currently central.  This is meant to stand in for the eventual requirement, imposed at typechecking time, that the intrinsic dimension of a higher field of a codatatype be central: such a dimension has to be able to go anywhere, and a map indexed by all the ways of matching it with an evaluation dimension needs that for all of them at once.  So it may be used only where the dimension in question is the intrinsic dimension of a higher field: partial bijections only ever index those, as does Insmap, but insertions in general do not, so insertion operations that are also called from elsewhere in core keep plain commutation. *)
let free_central : type g. g G.t -> g G.central = fun _ -> ()

let rec free_word_central : type n. n t -> n central = function
  | Word Zero -> Central_zero
  | Word (Suc (n, g)) -> Central_suc (free_word_central (Word n), g, free_central g)

let rec free_gen_commute : type g n. n t -> (g, n) gen_commute = function
  | Word Zero -> Commute_zero
  | Word (Suc (n, _)) -> Commute_suc (free_gen_commute (Word n), free_commute)

let rec free_word_commute : type m n. m t -> n t -> (m, n) commute =
 fun m n ->
  match m with
  | Word Zero -> Zero_commute
  | Word (Suc (m, _)) -> Suc_commute (free_word_commute (Word m) n, free_gen_commute n)

(* The unique generator witness for the (currently single-generator) dimension theory.  To prepare for future multi-generator generalization, consumers should refer to this rather than writing the constructor [Unit] directly. *)
let deg : unit G.t = G.Unit

(* Type-level natural numbers are represented by words over Unit, which are isomorphic to natural numbers.  The two-argument [suc] is inherited from Word; we only expose alias [one] and [two] for ergonomics in code that talks about specific small dimensions. *)
type one = (zero, unit) suc
type two = (one, unit) suc

let one : one t = suc zero deg
let two : two t = suc one deg

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
