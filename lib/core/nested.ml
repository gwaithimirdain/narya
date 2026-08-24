(* A deep match -- one whose patterns nest, or which matches several discriminees at once -- is compiled by the parser into a nest of matches, of which the user wrote only the outermost.  The nested ones are marked as such in the raw syntax (Raw's `Nested match sort), and what they become is decided here, when the match they are nested in is checked.

   The point is that the nest should be uniform.  A nested match becomes a convoy -- a match with an explicit motive, quantifying over the pattern variables that come after the one it matches and applied back to them -- whenever the match it is nested in has a motive of its own, whether the user's or the placeholder of a non-dependent one.  The convoy's motive is what refines those later variables' types, which is all an implicit match would have been doing there.  Only inside a match that is itself refining, an implicit one, do the nested matches stay implicit and refine in their turn.  The parser cannot decide this: whether refinement succeeds is not known until typechecking, and a match whose refinement fails becomes non-dependent.

   So the enclosing match publishes what it turned out to be while checking its branch bodies, and a nested match reads it.  A reader effect rather than a field of the status because the value is genuinely dynamically scoped: it must survive whatever lets and abstractions lie between a branch body and the nested match inside it, and must *not* survive into a match the user wrote there. *)
type t = [ `Implicit | `Convoy ]

module R = Algaeff.Reader.Make (struct
  type nonrec t = t
end)

let () = R.register_printer (function `Read -> Some "unhandled Nested.read effect")

(* Read what a nested match should become.  The default, outside any match, is to refine: a nested match with nothing to be nested in shouldn't arise, but if one does, behaving as the implicit match it used to be is the harmless choice. *)
let read () = R.read ()

(* Publish, while checking the branch bodies of a match, what that match turned out to be. *)
let run : type a. t -> (unit -> a) -> a = fun env f -> R.run ~env f
