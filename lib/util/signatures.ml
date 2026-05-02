module type Type = sig
  type t
end

module type Fam = sig
  type 'g t
end

module type Fam2 = sig
  type ('b, 'g) t
end

module type Fam3 = sig
  type ('a, 'b, 'c) t
end

module type Fam4 = sig
  type ('a, 'b, 'c, 'd) t
end

module type Fam5 = sig
  type ('a, 'b, 'c, 'd, 'e) t
end

module type Comparable = sig
  type 'g t

  val compare : 'g1 t -> 'g2 t -> ('g1, 'g2) Eq.compare
end

module type Function = sig
  module Dom : Fam
  module Cod : Fam

  type (_, _) t

  val dom : ('a, 'x) t -> 'a Dom.t
  val cod : ('a, 'x) t -> 'x Cod.t

  type _ exists = Exists : ('a, 'x) t -> 'a exists

  val exists : 'a Dom.t -> 'a exists
  val uniq : ('a, 'x1) t -> ('a, 'x2) t -> ('x1, 'x2) Eq.t
end

(* A parametrized family of functions. *)
module type Function2 = sig
  module Param : Fam
  module Dom : Fam
  module Cod : Fam

  type (_, _, _) t

  val dom : 'param Param.t -> ('param, 'a, 'x) t -> 'a Dom.t
  val cod : 'param Param.t -> ('param, 'a, 'x) t -> 'x Cod.t

  type (_, _) exists = Exists : ('param, 'a, 'x) t -> ('param, 'a) exists

  val exists : 'param Param.t -> 'a Dom.t -> ('param, 'a) exists
  val uniq : ('param, 'a, 'x1) t -> ('param, 'a, 'x2) t -> ('x1, 'x2) Eq.t
end

(* We deal with several kinds of intrinsically well-typed maps, whose output type depends on their input value (which is a type).  They all share this common signature. *)

module type MAP = sig
  module Key : Fam
  module F : Fam2

  type 'b t

  val empty : 'b t
  val find_opt : 'g Key.t -> 'b t -> ('b, 'g) F.t option
  val add : 'g Key.t -> ('b, 'g) F.t -> 'b t -> 'b t
  val update : 'g Key.t -> (('b, 'g) F.t option -> ('b, 'g) F.t option) -> 'b t -> 'b t
  val remove : 'g Key.t -> 'b t -> 'b t

  (* Mapping over intrinsically well-typed maps is complicated.  The mapping function has to be able to deal with any key, hence any parametrizing type for that key, so we have to wrap it up in a record with a polymorphic field.  Moreover, because some implementations of intrinsically well-typed maps shift the key parameter into a factor of the ambient parameter, there are issues with trying to change the ambient parameter.  Fortunately, for current applications, it suffices to keep that parameter the same. *)

  type 'a mapper = { map : 'g. 'g Key.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

  val map : 'a mapper -> 'a t -> 'a t

  (* Iterating is similar. *)

  type 'a iterator = { it : 'g. 'g Key.t -> ('a, 'g) F.t -> unit }

  val iter : 'a iterator -> 'a t -> unit
end

module type MAP_MAKER = sig
  module Key : Fam
  module Make : functor (F : Fam2) -> MAP with module Key := Key and module F := F
end
