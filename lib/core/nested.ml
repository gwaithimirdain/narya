(* A deep match -- one whose patterns nest, or which matches several discriminees at once -- is compiled by the parser into a nest of matches, of which the user wrote only the outermost.  The nested ones are marked as such in the raw syntax (Raw's `Nested match sort), and what they become is decided here, when the match they are nested in is checked.

   The point is that the nest should be uniform.  If the user gave the outermost match an explicit motive, the nested ones get explicit motives too -- convoys, since a nested match's later pattern variables may have types depending on the one it matches, so the motive has to quantify over them and the match be applied back to them.  If the user gave no motive, the nested ones refine like implicit matches.  And if the outermost ended up non-dependent, whether because the user said so or because refinement failed, so are the nested ones.  The parser cannot decide this itself: whether refinement succeeds is not known until typechecking.

   So the enclosing match publishes what it turned out to be while checking its branch bodies, and a nested match reads it.  A reader effect rather than a field of the status because the value is genuinely dynamically scoped: it must survive whatever lets and abstractions lie between a branch body and the nested match inside it, and must *not* survive into a match the user wrote there. *)
type t = [ `Implicit | `Nondep | `Convoy ]

module R = Algaeff.Reader.Make (struct
  type nonrec t = t
end)

let () = R.register_printer (function `Read -> Some "unhandled Nested.read effect")

(* Read what a nested match should become.  The default, outside any match, is to refine: a nested match with nothing to be nested in shouldn't arise, but if one does, behaving as the implicit match it used to be is the harmless choice. *)
let read () = R.read ()

(* Publish, while checking the branch bodies of a match, what that match turned out to be. *)
let run : type a. t -> (unit -> a) -> a = fun env f -> R.run ~env f
