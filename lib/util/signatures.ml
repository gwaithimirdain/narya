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

(* A Decidable is a Comparable whose comparison can also produce positive *apartness* witnesses: data (containing no closures, hence marshallable) attesting that two index types are distinct, which can be eliminated when combined with contradictory type-level equalities, so that impossible branches need no runtime assertions. *)
module type Decidable = sig
  include Comparable

  type ('g1, 'g2) apart

  type (_, _) decision =
    | Same : ('g, 'g) decision
    | Distinct : ('g1, 'g2) apart -> ('g1, 'g2) decision

  val decide : 'g1 t -> 'g2 t -> ('g1, 'g2) decision
  val apart_irrefl : ('g, 'g) apart -> Empty.t
end

module type Permutable = sig
  include Comparable

  type ('g, 'h) commute

  val commute_inv : 'g t -> 'h t -> ('g, 'h) commute -> ('h, 'g) commute
  val commute : 'g t -> 'h t -> ('g, 'h) commute option

  (* A generator is *central* if it commutes with every generator whatsoever.  This is stronger than commuting with any particular one, and is what is needed by structures indexed by all the ways of inserting a generator somewhere, which have to make sense of every position at once. *)
  type 'g central

  val central_commute : 'g t -> 'h t -> 'g central -> ('g, 'h) commute
  val centrality : 'g t -> 'g central option
end

module type DecidablePermutable = sig
  include Permutable
  include Decidable with type 'a t := 'a t
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

(* A function that also acts on permutable structure has to say how it transports witnesses of commutation.  The domain and codomain notions of commutation are left abstract here, since Dom and Cod are only Fams; users instantiate them with the appropriate ones. *)
module type PermFunction = sig
  include Function

  type ('a, 'b) dom_commute
  type ('x, 'y) cod_commute

  val commute : ('a, 'x) t -> ('b, 'y) t -> ('a, 'b) dom_commute -> ('x, 'y) cod_commute
end

(* A parametrized family of functions. *)
module type Function2 = sig
  module Param : Fam
  module Dom : Fam
  module Cod : Fam

  type (_, _, _) t

  val dom : ('param, 'a, 'x) t -> 'a Dom.t
  val cod : 'param Param.t -> ('param, 'a, 'x) t -> 'x Cod.t

  type (_, _) exists = Exists : ('param, 'a, 'x) t -> ('param, 'a) exists

  val exists : 'param Param.t -> 'a Dom.t -> ('param, 'a) exists
  val uniq : ('param, 'a, 'x1) t -> ('param, 'a, 'x2) t -> ('x1, 'x2) Eq.t
end

module type PermFunction2 = sig
  include Function2

  type ('a, 'b) dom_commute
  type ('x, 'y) cod_commute

  (* As with cod, computing the image commutation may need the parameter. *)
  val commute :
    'param Param.t ->
    ('param, 'a, 'x) t ->
    ('param, 'b, 'y) t ->
    ('a, 'b) dom_commute ->
    ('x, 'y) cod_commute

  (* Some clients also need to reflect commutation backwards along the function, to transfer an insertion in the codomain to one in the domain. *)
  val uncommute :
    ('param, 'a, 'x) t -> ('param, 'b, 'y) t -> ('x, 'y) cod_commute -> ('a, 'b) dom_commute
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

(* A similar interface for intrinsically well-typed maps with triply-parametrized keys.  The value family takes one additional parameter alongside the three key parameters. *)

module type MAP3 = sig
  module Key : Fam3
  module F : Fam4

  type 'p t

  val empty : 'p t
  val find_opt : ('a, 'b, 'c) Key.t -> 'p t -> ('p, 'a, 'b, 'c) F.t option
  val add : ('a, 'b, 'c) Key.t -> ('p, 'a, 'b, 'c) F.t -> 'p t -> 'p t

  val update :
    ('a, 'b, 'c) Key.t ->
    (('p, 'a, 'b, 'c) F.t option -> ('p, 'a, 'b, 'c) F.t option) ->
    'p t ->
    'p t

  val remove : ('a, 'b, 'c) Key.t -> 'p t -> 'p t

  type 'p mapper = {
    map : 'a 'b 'c. ('a, 'b, 'c) Key.t -> ('p, 'a, 'b, 'c) F.t -> ('p, 'a, 'b, 'c) F.t;
  }

  val map : 'p mapper -> 'p t -> 'p t

  type 'p iterator = { it : 'a 'b 'c. ('a, 'b, 'c) Key.t -> ('p, 'a, 'b, 'c) F.t -> unit }

  val iter : 'p iterator -> 'p t -> unit
end

module type MAP3_MAKER = sig
  module Key : Fam3
  module Make : functor (F : Fam4) -> MAP3 with module Key := Key and module F := F
end
