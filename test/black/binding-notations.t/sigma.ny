import "prelude"

` A typed binder, dependent and non-dependent
echo (x : A) × B x
echo A × C
echo (x : A) × (y : A) × Id A x y
synth (x : A) × B x
def pr (p : (x : A) × B x) : A ≔ p .fst
echo pr

` The family needn't be written as an abstraction
echo Σ A B
echo Σ A (_ ↦ C)

` An ascription that is just a term of the type
def AA : Type ≔ A
echo AA × C

` Shadowing: the outer x is substituted under the binder x
axiom x : A
echo ((y ↦ (x : A) × Id A y x) : A → Type) x

` Untyped binders, possibly ascribed
echo ∃ x, B x
echo ∃ (x : A), B x
echo ∃ _, C
echo ex B

` A binder after its body, and two binders in one abstraction
axiom int : (A → A) → A
notation(1) "∫" f "d" x ≔ int (x ↦ f)
echo ∫ x d x
axiom curry : (A → A → A) → A
notation(0) "λ²" x "," y "." b ≔ curry (x y ↦ b)
echo λ² x, y . x

` A constructor
def Tree : Type ≔ data [ leaf. | node. (f : A → Tree) ]
notation(0) "node" x "," t … ≔ node. (x ↦ t)
def t : Tree ≔ node x, node y, leaf.
echo t
