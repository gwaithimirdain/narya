axiom A : Type

` A variable of the context of a hole can't be renamed, so a constant that it would capture is displayed with the prefix _root_.
def K (A : Type) (y : _root_.A) : _root_.A ≔ ?

` Even where that variable is not in scope, so that the display doesn't depend on the order of the context.
def L (z : A) (A : Type) : Type ≔ ?
