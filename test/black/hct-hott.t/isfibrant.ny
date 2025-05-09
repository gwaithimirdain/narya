{` Requires command-line flag "-direction p,rel,Br" `}

{` Fibrancy is a higher coinductive predicate: an identification of fibrant types comes with transport and lifting functions in both directions, and its underlying correspondence is also fibrant. `}
def isFibrant (A : Type) : Type ≔ codata [
| x .trr.p : A.0 → A.1
| x .trl.p : A.1 → A.0
| x .liftr.p : (a₀ : A.0) → A.2 a₀ (x.2 .trr a₀)
| x .liftl.p : (a₁ : A.1) → A.2 (x.2 .trl a₁) a₁
| x .id.p : (a₀ : A.0) (a₁ : A.1) → isFibrant (A.2 a₀ a₁) ]

{` A fibrant type is a type that is fibrant. `}
def Fib : Type ≔ sig ( t : Type, f : isFibrant t )

{` The bridge/identity types of a fibrant type are fibrant. `}
def Id𝕗 (A : Fib) (x y : A .t) : Fib ≔ (Br (A .t) x y, rel A .f .id x y)

{` Dependent version `}
def Idd𝕗 (A0 A1 : Fib) (A2 : Br Fib A0 A1) (a0 : A0 .t) (a1 : A1 .t) : Fib
  ≔ (A2 .t a0 a1, A2 .f .id a0 a1)

{` Basic higher groupoid operations, constructed as in cubical type theory. `}
def transport (A : Type) (B : A → Fib) (x y : A) (p : Br A x y)
  : B x .t → B y .t
  ≔ rel B x y p .f .trr

def concat (A : Fib) (x y z : A .t) (p : Br (A .t) x y) (q : Br (A .t) y z)
  : Br (A .t) x z
  ≔ rel (Id𝕗 A x) y z q .f .trr p

def inverse (A : Fib) (x y : A .t) (p : Br (A .t) x y) : Br (A .t) y x
  ≔ rel ((z ↦ Id𝕗 A z x) : A .t → Fib) x y p .f .trr (rel x)

def transport2 (A : Type) (B : A → Fib) (x y : A) (p q : Br A x y)
  (r : Br (Br A x y) p q) (b : B x .t)
  : Br (B y .t) (transport A B x y p b) (transport A B x y q b)
  ≔ B⁽ᵖᵖ⁾ x x (rel x) y y (rel y) p q r
      .f
      .id.2 b (transport A B x y p b) (rel B x y p .f .liftr b) b
        (transport A B x y q b) (rel B x y q .f .liftr b)
      .trr (rel b)

{` Uniform higher operations on squares, arising from higher coinductive fields `}
def refl_transport_1 (A : Type) (B : A → Fib) (x₀₀ x₀₁ : A)
  (x₀₂ : Br A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Br A x₁₀ x₁₁)
  (x₂₀ : Br A x₀₀ x₁₀) (x₂₁ : Br A x₀₁ x₁₁)
  (x₂₂ : Br (Br A) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀ .t)
  (y₁ : B x₀₁ .t) (y₂ : Br B x₀₀ x₀₁ x₀₂ .t y₀ y₁)
  : Br B x₁₀ x₁₁ x₁₂
  .t (transport A B x₀₀ x₁₀ x₂₀ y₀) (transport A B x₀₁ x₁₁ x₂₁ y₁)
  ≔ Br (Br B) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁ x₂₂ .f .trr.1 y₀ y₁ y₂

def refl_transport_2 (A : Type) (B : A → Fib) (x₀₀ x₀₁ : A)
  (x₀₂ : Br A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Br A x₁₀ x₁₁)
  (x₂₀ : Br A x₀₀ x₁₀) (x₂₁ : Br A x₀₁ x₁₁)
  (x₂₂ : Br (Br A) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀ .t)
  (y₁ : B x₁₀ .t) (y₂ : Br B x₀₀ x₁₀ x₂₀ .t y₀ y₁)
  : Br B x₀₁ x₁₁ x₂₁
  .t (transport A B x₀₀ x₀₁ x₀₂ y₀) (transport A B x₁₀ x₁₁ x₁₂ y₁)
  ≔ Br (Br B) x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁ x₂₂ .f .trr.2 y₀ y₁ y₂

{` Two-dimensional globular identity types (which compute to squares with rel on two sides). `}
def Id𝕗2 (A : Fib) (x y : A .t) (p q : Br (A .t) x y) : Fib
  ≔ Id𝕗 (Id𝕗 A x y) p q

{` The right identity law can be obtained by transporting along a cylinder. `}
def concat_p1 (A : Fib) (x y : A .t) (p : Br (A .t) x y)
  : Br (Br (A .t) x y) (concat A x y y p (rel y)) p
  ≔ rel ((q ↦ Id𝕗2 A x y q p) : Br (A .t) x y → Fib) p
        (concat A x y y p (rel y)) (rel (Id𝕗 A x) y y (rel y) .f .liftr p)
      .f
      .trr (rel p)

{` The Paulin-Möhring identity type eliminator, constructed as in cubical type theory. `}
def J (A : Fib) (a : A .t) (P : (y : A .t) → Br (A .t) a y → Fib)
  (pa : P a (rel a) .t) (b : A .t) (p : Br (A .t) a b)
  : P b p .t
  ≔
  let sq ≔ rel (Id𝕗 A a) a b p .f in
  let q ≔ sq .trr (rel a) in
  let s ≔ sq .liftr (rel a) in
  rel P a b q (rel a) p (sym s) .f .trr pa

{` The type of squares in a fibrant type is also fibrant. `}
def Sq𝕗 (A : Fib) (x00 x01 : A .t) (x02 : Br (A .t) x00 x01) (x10 x11 : A .t)
  (x12 : Br (A .t) x10 x11) (x20 : Br (A .t) x00 x10)
  (x21 : Br (A .t) x01 x11)
  : Fib
  ≔ (
  A⁽ᵖᵖ⁾ .t x00 x01 x02 x10 x11 x12 x20 x21,
  A⁽ᵖᵖ⁾ .f .id.1 x00 x01 x02 x10 x11 x12 .id x20 x21)

{` We can obtain connection squares by applying J to relexivity squares. `}
def conn (A : Fib) (x y : A .t) (p : Br (A .t) x y)
  : Sq𝕗 A x y p y y (rel y) p (rel y) .t
  ≔ J A x (z q ↦ Sq𝕗 A x z q z z (rel z) q (rel z)) (rel (rel x)) y p

def coconn (A : Fib) (x y : A .t) (p : Br (A .t) x y)
  : Sq𝕗 A x x (rel x) x y p (rel x) p .t
  ≔ J A x (z q ↦ Sq𝕗 A x x (rel x) x z q (rel x) q) (rel (rel x)) y p

{` Using a connection square, we can prove the left identity law by a similar cylindrical transport. `}
def concat_1p (A : Fib) (x y : A .t) (p : Br (A .t) x y)
  : Br (Br (A .t) x y) (concat A x x y (rel x) p) p
  ≔ rel (Id𝕗2 A x) x y p (rel x) (concat A x x y (rel x) p)
        (rel (Id𝕗 A x) x y p .f .liftr (rel x)) (rel x) p (coconn A x y p)
      .f
      .trr (rel (rel x))

{` Finally, we can prove the typal β-rule for the J-eliminator. `}
def Jβ (A : Fib) (a : A .t) (P : (y : A .t) → Br (A .t) a y → Fib)
  (pa : P a (rel a) .t)
  : Br (P a (rel a) .t) pa (J A a P pa a (rel a))
  ≔
  let sq ≔ rel (Id𝕗 A a) a a (rel a) .f in
  let q ≔ sq .trr (rel a) in
  let s ≔ sq .liftr (rel a) in
  let cube
    ≔ rel (Sq𝕗 A) a a (rel a) a a (rel a) (rel a) (rel a) a⁽ᵖᵖ⁾ a a (rel a) a
        a (rel a) (rel a) q s (rel a) (rel a) a⁽ᵖᵖ⁾ (rel a) (rel a) a⁽ᵖᵖ⁾ .f
    in
  let t ≔ cube .trr a⁽ᵖᵖ⁾ in
  let c ≔ cube .liftr a⁽ᵖᵖ⁾ in
  P⁽ᵖᵖ⁾ a a (rel a) a a (rel a) (rel a) q (sym t) (rel a) (rel a) a⁽ᵖᵖ⁾
      (rel a) (rel a) a⁽ᵖᵖ⁾ a⁽ᵖᵖ⁾ (sym s) c⁽³²¹⁾
    .f
    .id.2 pa pa (rel pa) pa (J A a P pa a (rel a))
      (rel P a a q (rel a) (rel a) (sym s) .f .liftr pa)
    .trr (rel pa)
