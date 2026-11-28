{` A notation whose arguments include a higher-dimensional one is used only if no implicit boundary argument would fall in one of its explicit slots `}
axiom A : Type
axiom a : A
axiom e : Id A a a
axiom f (x : A) : Id (A → A) (y ↦ y) (y ↦ y)
notation(5) "F" x "," y ≔ f x y
echo f a e
notation(5) "K" x ≔ f x
echo f a e

{` A top argument that doesn't synthesize is displayed with its boundary even when implicits are hidden `}
axiom g (x : A) : Id ((A → A) → A) (u ↦ u a) (u ↦ u a)
notation(5) "G" x "," y ≔ g x y
echo g a {y ↦ y} {y ↦ y} (y ⤇ y.2)
notation(5) "L" x ≔ g x
echo g a {y ↦ y} {y ↦ y} (y ⤇ y.2)
