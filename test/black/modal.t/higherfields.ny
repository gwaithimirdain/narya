{` -*- narya-prog-args: ("-proofgeneral" "-spatial") -*- `}

axiom A : Type

` A modal *higher* codatatype: the "amazing right adjoint" √ of the identity
` type, composed with the ♭-modal structure.  The field .root has intrinsic
` dimension 1 and is checked (like a lower modal field) in a context locked by
` the right adjoint ♯; ♭ is parametric, so it filters none of the field's
` intrinsic dimensions.
def √♭A : Type ≔ codata [ (x :♭| _) .root.e : A ]

` A projection is written with the locking left adjoint ♭ as an ascription, and
` its type is keyed by the adjunction counit into the ambient context.

axiom s0 : √♭A

axiom s1 : √♭A

axiom s2 : Id √♭A s0 s1

echo (s2 :♭| _) .root.1

` The suffix can be omitted when it's the identity.
echo (s2 :♭| _) .root

` At higher dimensions we can project along each direction of a square, and the
` boundaries are themselves modal projections of the boundary squares.

axiom s00 : √♭A

axiom s01 : √♭A

axiom s10 : √♭A

axiom s11 : √♭A

axiom s02 : Id √♭A s00 s01

axiom s12 : Id √♭A s10 s11

axiom s20 : Id √♭A s00 s10

axiom s21 : Id √♭A s01 s11

axiom s22 : √♭A⁽ᵉᵉ⁾ s02 s12 s20 s21

echo (s22 :♭| _) .root.1

echo (s22 :♭| _) .root.2
