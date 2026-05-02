(* Module signatures for type-level (additive) monoids. *)

module type Monoid = sig
  (* The elements of the monoid are the types that satisfy this predicate. *)
  type 'a t
  type wrapped = Wrap : 'a t -> wrapped

  val compare : 'a t -> 'b t -> ('a, 'b) Eq.compare

  (* Addition defined as a relation *)
  type ('a, 'b, 'c) plus

  (* To compute a sum, we wrap up the output in a GADT. *)
  type (_, _) has_plus = Plus : ('a, 'b, 'c) plus -> ('a, 'b) has_plus

  (* The conditions on which of these have to be assumed and which are deduced follows what happens for type-level natural numbers.  If we had other examples, we might have to be more flexible. *)
  val plus : 'b t -> ('a, 'b) has_plus
  val plus_right : ('a, 'b, 'c) plus -> 'b t
  val plus_left : ('m, 'n, 'mn) plus -> 'mn t -> 'm t
  val plus_out : 'a t -> ('a, 'b, 'c) plus -> 'c t

  (* Sums are unique *)
  val plus_uniq : ('a, 'b, 'c) plus -> ('a, 'b, 'd) plus -> ('c, 'd) Eq.t

  (* The unit element of the monoid is called zero *)
  type zero

  val zero : zero t
  val zero_plus : 'a t -> (zero, 'a, 'a) plus
  val plus_zero : 'a t -> ('a, zero, 'a) plus

  (* Addition is associative *)
  val plus_assocl :
    ('a, 'b, 'ab) plus -> ('b, 'c, 'bc) plus -> ('a, 'bc, 'abc) plus -> ('ab, 'c, 'abc) plus

  val plus_assocr :
    ('a, 'b, 'ab) plus -> ('b, 'c, 'bc) plus -> ('ab, 'c, 'abc) plus -> ('a, 'bc, 'abc) plus
end

(* Monoids with positivity (i.e. nonzero-ness) predicate *)

(* We first define a "mixin" module, where the types needed from Monoid are abstract, and then combine it with Monoid using a destructive substitution.  This makes it possible to combine multiple mixins at once without a diamond problem. *)
module type Pos = sig
  type 'a t
  type zero
  type ('a, 'b, 'ab) plus

  (* A subtype of elements of the monoid called "positive" *)
  type _ pos

  val pos : 'a pos -> 'a t

  (* Zero is not positive.  We assert this by explosion. *)
  val zero_nonpos : zero pos -> 'c

  (* Adding a positive element to anything remains positive. *)
  val plus_pos : 'a t -> 'b pos -> ('a, 'b, 'ab) plus -> 'ab pos
  val pos_plus : 'a pos -> ('a, 'b, 'ab) plus -> 'ab pos

  (* Everything is either zero or positive. *)
  type _ compare_zero = Zero : zero compare_zero | Pos : 'n pos -> 'n compare_zero

  val compare_zero : 'a t -> 'a compare_zero
end

module type MonoidPos = sig
  include Monoid

  include
    Pos
      with type 'a t := 'a t
       and type zero := zero
       and type ('a, 'b, 'ab) plus := ('a, 'b, 'ab) plus
end

(* Monoids with permutations (symmetric strict monoidal categories) *)

module type Perm = sig
  type 'a t
  type ('a, 'b, 'ab) plus
  type ('a, 'b) permute

  val perm_dom : ('a, 'b) permute -> 'b t -> 'a t
  val perm_id : 'a t -> ('a, 'a) permute
  val perm_swap : ('a, 'b, 'ab) plus -> ('b, 'a, 'ba) plus -> ('ab, 'ba) permute
  val perm_comp : ('a, 'b) permute -> ('b, 'c) permute -> ('a, 'c) permute
  val perm_inv : ('a, 'b) permute -> ('b, 'a) permute

  val perm_plus :
    ('a, 'b, 'ab) plus ->
    ('c, 'd, 'cd) plus ->
    ('a, 'c) permute ->
    ('b, 'd) permute ->
    ('ab, 'cd) permute
end

module type MonoidPerm = sig
  include Monoid
  include Perm with type 'a t := 'a t and type ('a, 'b, 'ab) plus := ('a, 'b, 'ab) plus
end

(* Monoids with forwards-ness *)

module type Fwd = sig
  type 'a t
  type ('a, 'b, 'ab) plus
  type 'a fwd
  type fwd_zero

  val fwd_zero : fwd_zero fwd

  (* backwards + forwards = backwards *)
  type ('a, 'b, 'ab) bplus
  type (_, _) has_bplus = Bplus : ('a, 'b, 'ab) bplus -> ('a, 'b) has_bplus

  val bplus : 'b fwd -> ('a, 'b) has_bplus
  val bplus_zero : 'a t -> ('a, fwd_zero, 'a) bplus

  (* backwards + forwards = forwards *)
  type ('a, 'b, 'ab) fplus

  val bfplus_assocr :
    ('a, 'b, 'ab) plus -> ('b, 'c, 'bc) fplus -> ('ab, 'c, 'abc) bplus -> ('a, 'bc, 'abc) bplus
end

module type MonoidFwd = sig
  include Monoid
  include Fwd with type 'a t := 'a t and type ('a, 'b, 'ab) plus := ('a, 'b, 'ab) plus
end

(* Monoids with permutations AND forwards-ness *)

module type MonoidPermFwd = sig
  include Monoid
  include Perm with type 'a t := 'a t and type ('a, 'b, 'ab) plus := ('a, 'b, 'ab) plus
  include Fwd with type 'a t := 'a t and type ('a, 'b, 'ab) plus := ('a, 'b, 'ab) plus
end
