(* Type-level backwards lists.  Only the type constructors live here; the operations on backwards lists of a specific sort belong to whatever structure indexes them, namely Word (free monoids, whose elements are backwards lists of generators) and Path (free categories, whose morphisms are backwards lists of composable edges). *)

type emp = private Dummy_emp
type ('xs, 'x) snoc = private Dummy_snoc
