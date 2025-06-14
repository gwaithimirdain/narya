{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

{` Basic higher groupoid operations, constructed as in cubical type theory. `}

def transport (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  : B x → B y
  ≔ refl B p .trr.1

def concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z) : Id A x z
  ≔ refl ((y ↦ Id A x y) : A → Type) q .trr.1 p

def inverse (A : Type) (x y : A) (p : Id A x y) : Id A y x
  ≔ refl ((z ↦ Id A z x) : A → Type) p .trr.1 (refl x)

def transport2 (A : Type) (B : A → Type) (x y : A) (p q : Id A x y)
  (r : Id (Id A x y) p q) (b : B x)
  : Id (B y) (transport A B x y p b) (transport A B x y q b)
  ≔ sym (B⁽ᵉᵉ⁾ r) (refl B p .liftr.1 b) (refl B q .liftr.1 b)
      .trr.1 (refl b)

{` Uniform higher operations on squares `}
def refl_transport_1 (A : Type) (B : A → Type) (x₀₀ x₀₁ : A)
  (x₀₂ : Id A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
  (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁)
  (x₂₂ : Id (Id A) x₀₂ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀) (y₁ : B x₀₁)
  (y₂ : Id B x₀₂ y₀ y₁)
  : Id B x₁₂ (transport A B x₀₀ x₁₀ x₂₀ y₀) (transport A B x₀₁ x₁₁ x₂₁ y₁)
  ≔ Id (Id B) x₂₂ .trr.1 y₂

def refl_transport_2 (A : Type) (B : A → Type) (x₀₀ x₀₁ : A)
  (x₀₂ : Id A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
  (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁)
  (x₂₂ : Id (Id A) x₀₂ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀) (y₁ : B x₁₀)
  (y₂ : Id B x₂₀ y₀ y₁)
  : Id B x₂₁ (transport A B x₀₀ x₀₁ x₀₂ y₀) (transport A B x₁₀ x₁₁ x₁₂ y₁)
  ≔ Id (Id B) x₂₂ .trr.2 y₂

{` Two-dimensional globular identity types (which compute to squares with refl on two sides). `}
def Id2 (A : Type) (x y : A) (p q : Id A x y) : Type ≔ Id (Id A x y) p q

{` The right identity law can be obtained by transporting along a cylinder. `}
def concat_p1 (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x y y p (refl y)) p
  ≔ refl ((q ↦ Id2 A x y q p) : Id A x y → Type)
        (refl ((z ↦ Id A x z) : A → Type) (refl y) .liftr.1 p)
      .trr.1 (refl p)

{` The Paulin-Möhring identity type eliminator, constructed as in cubical type theory. `}
def J (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (pa : P a (refl a)) (b : A) (p : Id A a b)
  : P b p
  ≔
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) p in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  refl P q (sym s) .trr.1 pa

{` The type of squares in a type. `}
def Sq (A : Type) (x00 x01 : A) (x02 : Id A x00 x01) (x10 x11 : A)
  (x12 : Id A x10 x11) (x20 : Id A x00 x10) (x21 : Id A x01 x11)
  : Type
  ≔ A⁽ᵉᵉ⁾ x02 x12 x20 x21

{` We can obtain connection squares by applying J to reflexivity squares. `}
def conn (A : Type) (x y : A) (p : Id A x y)
  : Sq A x y p y y (refl y) p (refl y)
  ≔ J A x (z q ↦ Sq A x z q z z (refl z) q (refl z)) (refl (refl x)) y p

def coconn (A : Type) (x y : A) (p : Id A x y)
  : Sq A x x (refl x) x y p (refl x) p
  ≔ J A x (z q ↦ Sq A x x (refl x) x z q (refl x) q) (refl (refl x)) y p

{` Using a connection square, we can prove the left identity law by a similar cylindrical transport. `}
def concat_1p (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x x y (refl x) p) p
  ≔ refl (Id2 A x) p (refl ((z ↦ Id A x z) : A → Type) p .liftr.1 (refl x))
        (coconn A x y p)
      .trr.1 (refl (refl x))

{` Finally, we can prove the typal β-rule for the J-eliminator. `}
def Jβ (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (pa : P a (refl a))
  : Id (P a (refl a)) pa (J A a P pa a (refl a))
  ≔
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) (refl a) in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  let cube
    ≔ refl (Sq A) (refl a) (refl a) a⁽ᵉᵉ⁾ (refl a) (refl a) s a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾
    in
  let t ≔ cube .trr.1 a⁽ᵉᵉ⁾ in
  let c ≔ cube .liftr.1 a⁽ᵉᵉ⁾ in
  sym (P⁽ᵉᵉ⁾ (sym t) c⁽³²¹⁾) (refl pa) (refl P q (sym s) .liftr.1 pa)
    .trr.1 (refl pa)
