{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

axiom A₀ : Type
axiom A₁ : Type
axiom A₂ : Id Type A₀ A₁

axiom B₀ : Type
axiom B₁ : Type
axiom B₂ : Id Type B₀ B₁

axiom R₀ : A₀ → B₀ → Type
axiom Rb₀ : isBisim A₀ B₀ R₀

axiom R₁ : A₁ → B₁ → Type
axiom Rb₁ : isBisim A₁ B₁ R₁

axiom R₂ : ((x : A₂) (y : B₂) ⇒ Id Type) R₀ R₁
axiom Rb₂ : refl isBisim A₂ B₂ R₂ Rb₀ Rb₁

axiom a₀ : A₀
axiom a₁ : A₁
axiom a₂ : A₂ a₀ a₁

axiom b₀ : B₀
axiom b₁ : B₁
axiom b₂ : B₂ b₀ b₁

axiom r₀ : R₀ a₀ b₀
axiom r₁ : R₁ a₁ b₁
axiom r₂ : R₂ a₂ b₂ r₀ r₁

def G₀ : Id Type A₀ B₀ ≔ glue A₀ B₀ R₀ Rb₀
def G₁ : Id Type A₁ B₁ ≔ glue A₁ B₁ R₁ Rb₁
def G₂ : Id (Id Type) A₂ B₂ G₀ G₁ ≔ refl glue A₂ B₂ R₂ Rb₂

def g₀ : G₀ a₀ b₀ ≔ (r₀,)
def g₁ : G₁ a₁ b₁ ≔ (r₁,)
def g₂ : G₂ a₂ b₂ g₀ g₁ ≔ (r₂,)

echo G₂ .trr.1
def trr1 : Id (B₂ (Rb₀ .trr a₀) (Rb₁ .trr a₁)) (G₂ .trr.1 a₂) (Rb₂ .trr a₂)
  ≔ refl _

echo G₂ .trl.1
def trl1 : Id (A₂ (Rb₀ .trl b₀) (Rb₁ .trl b₁)) (G₂ .trl.1 b₂) (Rb₂ .trl b₂)
  ≔ refl _

echo G₂ .liftr.1
def liftr1
  : Id
      (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂ a₂ (Rb₂ .trr a₂) (_ ≔ Rb₀ .liftr a₀)
         (_ ≔ Rb₁ .liftr a₁)) (G₂ .liftr.1 a₂) (_ ≔ Rb₂ .liftr a₂)
  ≔ refl _

echo G₂ .liftl.1
def liftl1
  : Id
      (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂ (Rb₂ .trl b₂) b₂ (_ ≔ Rb₀ .liftl b₀)
         (_ ≔ Rb₁ .liftl b₁)) (G₂ .liftl.1 b₂) (_ ≔ Rb₂ .liftl b₂)
  ≔ refl _

echo G₂ .trr.2
def trr2
  : Id (G₁ (A₂ .trr a₀) (B₂ .trr b₀)) (G₂ .trr.2 g₀)
      (_ ≔ R₂ (A₂ .liftr a₀) (B₂ .liftr b₀) .trr r₀)
  ≔ refl _

echo G₂ .trl.2
def trl2
  : Id (G₀ (A₂ .trl a₁) (B₂ .trl b₁)) (G₂ .trl.2 g₁)
      (_ ≔ R₂ (A₂ .liftl a₁) (B₂ .liftl b₁) .trl r₁)
  ≔ refl _

echo G₂ .liftr.2
def liftr2
  : Id
      (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) g₀ {A₂ .trr a₀} {B₂ .trr b₀}
         (_ ≔ R₂ (A₂ .liftr a₀) (B₂ .liftr b₀) .trr r₀) (A₂ .liftr a₀)
         (B₂ .liftr b₀)) (G₂ .liftr.2 g₀)
      (sym (_ ≔ R₂ (A₂ .liftr a₀) (B₂ .liftr b₀) .liftr r₀))
  ≔ refl _

echo G₂ .liftl.2
def liftl2
  : Id
      (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) {A₂ .trl a₁} {B₂ .trl b₁}
         (_ ≔ R₂ (A₂ .liftl a₁) (B₂ .liftl b₁) .trl r₁) g₁ (A₂ .liftl a₁)
         (B₂ .liftl b₁)) (G₂ .liftl.2 g₁)
      (sym (_ ≔ R₂ (A₂ .liftl a₁) (B₂ .liftl b₁) .liftl r₁))
  ≔ refl _

echo G₂ a₂ b₂ .trr
def abtrr : Id (G₁ a₁ b₁) (G₂ a₂ b₂ .trr g₀) (_ ≔ R₂ a₂ b₂ .trr r₀)
  ≔ refl _

echo G₂ a₂ b₂ .trl
def abtrl : Id (G₀ a₀ b₀) (G₂ a₂ b₂ .trl g₁) (_ ≔ R₂ a₂ b₂ .trl r₁)
  ≔ refl _

echo G₂ a₂ b₂ .liftr
def abliftr
  : Id (G₂ a₂ b₂ g₀ (_ ≔ R₂ a₂ b₂ .trr r₀)) (G₂ a₂ b₂ .liftr g₀)
      ((_ ≔ R₂ a₂ b₂ .liftr r₀))
  ≔ refl _

echo G₂ a₂ b₂ .liftl
def abliftl
  : Id (G₂ a₂ b₂ (_ ≔ R₂ a₂ b₂ .trl r₁) g₁) (G₂ a₂ b₂ .liftl g₁)
      ((_ ≔ R₂ a₂ b₂ .liftl r₁))
  ≔ refl _

echo sym G₂ g₀ g₁ .trr
def ggtrr
  : Id (B₂ b₀ b₁) (sym G₂ g₀ g₁ .trr a₂)
      (Rb₂ .id a₀ b₀ r₀ a₁ b₁ r₁ .trr a₂)
  ≔ refl _

echo sym G₂ g₀ g₁ .trl
def ggtrl
  : Id (A₂ a₀ a₁) (sym G₂ g₀ g₁ .trl b₂)
      (Rb₂ .id a₀ b₀ r₀ a₁ b₁ r₁ .trl b₂)
  ≔ refl _

echo sym G₂ g₀ g₁ .liftr
def ggliftr
  : Id
      (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) g₀ g₁ a₂
         (Rb₂ .id a₀ b₀ r₀ a₁ b₁ r₁ .trr a₂)) (sym G₂ g₀ g₁ .liftr a₂)
      (sym (_ ≔ Rb₂ .id a₀ b₀ r₀ a₁ b₁ r₁ .liftr a₂))
  ≔ refl _

echo sym G₂ g₀ g₁ .liftl
def ggliftl
  : Id
      (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) g₀ g₁ (Rb₂ .id a₀ b₀ r₀ a₁ b₁ r₁ .trl b₂)
         b₂) (sym G₂ g₀ g₁ .liftl b₂)
      (sym (_ ≔ Rb₂ .id a₀ b₀ r₀ a₁ b₁ r₁ .liftl b₂))
  ≔ refl _

