Printing higher-dimensional pi-types

  $ cat >hdpi.ny <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom E : Id Type A B
  > axiom A' : A → Type
  > axiom B' : B → Type
  > axiom E' : refl ((X ↦ X → Type) : Type → Type) E A' B'
  > echo refl ((A B ↦ (x:A) → B x) : (X:Type) → (X → Type) → Type) E E'
  > EOF

  $ narya hdpi.ny
  (x : E) ⇒ E' x.2
    : Type⁽ᵉ⁾ ((x : A) → A' x) ((x : B) → B' x)
  
