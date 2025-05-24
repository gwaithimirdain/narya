Testing parsing and printing of cube variables

  $ cat >cube_vars.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom b:B
  > def f : A -> B := x |-> b
  > def g (x:A) : B := b
  > def fg : Id (A -> B) f g := x0 x1 x2 |-> refl b
  > echo (x0 x1 x2 |-> fg x2) : Id (A -> B) f g
  > echo (x00 x01 x02 x10 x11 x12 x20 x21 x22 |-> refl fg x22) : Id (Id (A -> B) f g) fg fg
  > echo (x |=> fg x.2) : Id (A -> B) f g
  > echo ((x |=> refl fg x.22) : Id (Id (A -> B) f g) fg fg)
  > axiom h (x:A) : Id B b b
  > def fgh : Id (A -> B) f g := x0 x1 x2 |-> h x0
  > echo (x0 x1 x2 |-> fgh x2) : Id (A -> B) f g
  > echo (x |=> fgh x.2) : Id (A -> B) f g
  > echo ((x |=> refl fgh x.22) : Id (Id (A -> B) f g) fgh fgh)
  > echo ((x |=> refl h x.02) : Id (Id (A -> B) f g) fgh fgh)
  > axiom a0:A
  > axiom a1:A
  > axiom a2:Id A a0 a1
  > echo refl f a2
  > EOF

  $ narya cube_vars.ny
  x0 x1 x2 ↦ refl b
    : refl Π (refl A) {_ ↦ B} {_ ↦ B} (_ ⤇ refl B) f g
  
  x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦ b⁽ᵉᵉ⁾
    : Π⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ {_ ↦ B} {_ ↦ B} {_ ⤇ refl B} {_ ↦ B} {_ ↦ B} {_ ⤇ refl B}
        {_ ⤇ refl B} {_ ⤇ refl B} (_ ⤇ B⁽ᵉᵉ⁾) (refl f) (refl g) fg fg
  
  x ⤇ refl b
    : refl Π (refl A) {_ ↦ B} {_ ↦ B} (_ ⤇ refl B) f g
  
  x ⤇ b⁽ᵉᵉ⁾
    : Π⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ {_ ↦ B} {_ ↦ B} {_ ⤇ refl B} {_ ↦ B} {_ ↦ B} {_ ⤇ refl B}
        {_ ⤇ refl B} {_ ⤇ refl B} (_ ⤇ B⁽ᵉᵉ⁾) (refl f) (refl g) fg fg
  
  x0 x1 x2 ↦ h x0
    : refl Π (refl A) {_ ↦ B} {_ ↦ B} (_ ⤇ refl B) f g
  
  x ⤇ h x.0
    : refl Π (refl A) {_ ↦ B} {_ ↦ B} (_ ⤇ refl B) f g
  
  x ⤇ refl h x.02
    : Π⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ {_ ↦ B} {_ ↦ B} {_ ⤇ refl B} {_ ↦ B} {_ ↦ B} {_ ⤇ refl B}
        {_ ⤇ refl B} {_ ⤇ refl B} (_ ⤇ B⁽ᵉᵉ⁾) (refl f) (refl g) fgh fgh
  
  x ⤇ refl h x.02
    : Π⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ {_ ↦ B} {_ ↦ B} {_ ⤇ refl B} {_ ↦ B} {_ ↦ B} {_ ⤇ refl B}
        {_ ⤇ refl B} {_ ⤇ refl B} (_ ⤇ B⁽ᵉᵉ⁾) (refl f) (refl g) fgh fgh
  
  refl b
    : refl B b b
  
