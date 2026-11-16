(* The exception by which parsers fail.  It is private to this library: client code fails with the combinators "fail" and "unexpected", and only the combinators of this library catch it. *)
exception Fail

(* The signature of the type parameters of the parser functors. *)
module type ANY = sig
  type t
end
