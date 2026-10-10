open Util
open Asai.Range

(* Our notion of raw term is parametrized over a notion of "index".  Narya proper only uses ordinary type-level natural numbers as indices, but other frontends may need a notion of raw term that uses explicit names or something else.  All raw terms clearly separate *variables* from *constants*, and the "resolution" process that transitions between them preserves this distinction.  Therefore, even raw terms that use "explicit names" should not be regarded as an "intermediate parsing step" before turning the names into indices, because a scope of local variables is already required to separate the variables from the constant names (since local variables can shadow global constants).  Instead it is better to think of them as more like the "values" in NbE which can be silently weakened to arbitrary contexts. *)

module type Indices = sig
  (* A 'name' is what labels a variable at the point of *binding*.  In named terms this carries semantic information; in indexed terms it is just annotation, with the semantic information carried by the change in the parametrizing type. *)
  type name

  (* There must be unnamed variables. *)
  val none : name

  (* These are how the parametrizing type changes with each bound variable. *)
  type 'a suc

  (* An 'index' is what labels a variable at the point of *use*. *)
  type 'a index

  (* A 'scope' represents the local variables available, usually as a list or vector of names.  This is only used as something to store with a Hole. *)
  type 'a scope

  (* We also allow embedding an arbitrary object. *)
  type 'a embed
end

(* This is the standard instantiation that uses type-level nats as De Bruijn indices. *)
module DeBruijnIndices = struct
  type name = string option

  let none : name = None

  type 'a index = 'a N.index
  type 'a suc = 'a N.suc
  type 'a scope = (name, 'a) Bwv.t
  type 'a embed = |
end

(* We need a version of 'bplus' that applies the arbitrary notion of 'successor' for any kind of indices. *)
module Bplus (I : Indices) = struct
  type ('a, 'b, 'ab) bplus =
    | Zero : ('a, Fwn.zero, 'a) bplus
    | Suc : ('a I.suc, 'b, 'ab) bplus -> ('a, 'b Fwn.suc, 'ab) bplus

  let bplus_zero : type a ab. (a, Fwn.zero, ab) bplus -> (a, ab) Eq.t = function
    | Zero -> Eq

  let bplus_suc : type a b ab. (a, b Fwn.suc, ab) bplus -> (a I.suc, b, ab) bplus = function
    | Suc ab -> ab

  let rec bplus_right : type a b ab. (a, b, ab) bplus -> b Fwn.t = function
    | Zero -> Zero
    | Suc ab -> Suc (bplus_right ab)

  type ('a, 'b) has_bplus = Bplus : ('a, 'b, 'ab) bplus -> ('a, 'b) has_bplus

  let rec bplus : type a b. b Fwn.t -> (a, b) has_bplus = function
    | Zero -> Bplus Zero
    | Suc b ->
        let (Bplus ab) = bplus b in
        Bplus (Suc ab)

  type ('a, 'ab) has_bplus_to = Bplus_to : ('a, 'b, 'ab) bplus -> ('a, 'ab) has_bplus_to

  (* Prepend the variables counted by a bplus to another bplus, forgetting the total count. *)
  let rec prepend_bplus : type a c ac ab.
      (a, c, ac) bplus -> (ac, ab) has_bplus_to -> (a, ab) has_bplus_to =
   fun ac rest ->
    match ac with
    | Zero -> rest
    | Suc ac ->
        let (Bplus_to b) = prepend_bplus ac rest in
        Bplus_to (Suc b)
end

(* A special kind of Vector of names that raises the parametrizing indices as we go, and also stores the bplus of the starting index with the length.  This simplifies things in a few places where otherwise we would have to store a bplus along with a vector of names to get the correct extended context length for bodies of terms under multiple binders. *)
module Namevec (I : Indices) = struct
  module P = Bplus (I)
  open P

  type (_, _, _) t =
    | [] : ('a, Fwn.zero, 'a) t
    | ( :: ) : I.name * ('a I.suc, 'b, 'ab) t -> ('a, 'b Fwn.suc, 'ab) t

  let rec length : type a b ab. (a, b, ab) t -> b Fwn.t = function
    | [] -> Zero
    | _ :: xs -> Suc (length xs)

  let rec bplus : type a b ab. (a, b, ab) t -> (a, b, ab) bplus = function
    | [] -> Zero
    | _ :: xs -> Suc (bplus xs)

  let rec none : type a b ab. (a, b, ab) bplus -> (a, b, ab) t =
   fun ab ->
    match bplus_right ab with
    | Zero ->
        let Eq = bplus_zero ab in
        []
    | Suc _ ->
        let ab = bplus_suc ab in
        I.none :: none ab

  let rec of_vec : type a b ab. (a, b, ab) bplus -> (I.name, b) Vec.t -> (a, b, ab) t =
   fun ab xs ->
    match (ab, xs) with
    | Zero, [] -> []
    | Suc ab, x :: xs -> x :: of_vec ab xs

  let rec to_list : type a b ab. (a, b, ab) t -> I.name list = function
    | [] -> []
    | x :: xs -> x :: to_list xs
end

(* The pattern variables of one branch of a match: one entry for each argument of the constructor, which is either a single variable (which for a higher-dimensional match is a cube variable, with its boundary accessed by face suffixes) or an explicit list of variables naming all the faces of its boundary, the last of which is the top face.  The middle index counts the *arguments*, hence is the arity of the constructor, while the last index is the raw context extended by all the variables actually bound. *)
module Patternvars (I : Indices) = struct
  module Namevec = Namevec (I)
  open Namevec.P

  (* The pattern variables of a single argument, forgetting how many arguments remain. *)
  type (_, _) arg =
    | Cube : I.name -> ('a, 'a I.suc) arg
    | Boundary : ('a, 'c, 'ac) Namevec.t located -> ('a, 'ac) arg

  type (_, _, _) t =
    | [] : ('a, Fwn.zero, 'a) t
    | ( :: ) : ('a, 'a1) arg * ('a1, 'b, 'ab) t -> ('a, 'b Fwn.suc, 'ab) t

  let rec length : type a b ab. (a, b, ab) t -> b Fwn.t = function
    | [] -> Zero
    | _ :: xs -> Suc (length xs)

  (* The total number of variables bound, which is more than the number of arguments if any of them have explicit boundaries. *)
  let rec bplus : type a b ab. (a, b, ab) t -> (a, ab) has_bplus_to = function
    | [] -> Bplus_to Zero
    | Cube _ :: xs ->
        let (Bplus_to ab) = bplus xs in
        Bplus_to (Suc ab)
    | Boundary ns :: xs -> prepend_bplus (Namevec.bplus ns.value) (bplus xs)

  let rec none : type a b ab. (a, b, ab) bplus -> (a, b, ab) t =
   fun ab ->
    match bplus_right ab with
    | Zero ->
        let Eq = bplus_zero ab in
        []
    | Suc _ -> Cube I.none :: none (bplus_suc ab)

  (* Whether every argument has its boundary given explicitly, so that no cube variables are bound.  (Vacuously true for a constructor with no arguments.) *)
  let rec all_boundary : type a b ab. (a, b, ab) t -> bool = function
    | [] -> true
    | Cube _ :: _ -> false
    | Boundary _ :: xs -> all_boundary xs
end

module IndexedNamevec = Namevec (DeBruijnIndices)
module IndexedPatternvars = Patternvars (DeBruijnIndices)
