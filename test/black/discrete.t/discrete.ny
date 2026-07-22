{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

` The modality ♭ is a *discrete* comonad: working under a ♭ lock filters
` out the parametric dimensions.  We set up the usual comonad structure, plus a
` non-modal type family T for contrast with the modal family ♭.

def f (A :♭| Type) (x :♭| A) : A ≔ x

def ♭ (A :♭| Type) : Type ≔ data [ flat. (x :♭| A) ]

def ♭map (A B :♭| Type) (g :♭| A → B) : ♭ A → ♭ B ≔ [
| flat. x ↦ flat. (g x)]

def ε (A :♭| Type) (u : ♭ A) : A ≔ match u [ flat. x ↦ x ]

def δ (A :♭| Type) (u : ♭ A) : ♭ (♭ A) ≔ match u [
| flat. x ↦ flat. (flat. x)]

` A non-modal family, whose refl has an unfiltered (square) domain.
def T (A : Type) : Type ≔ data [ mk. (x : A) ]

` The parametricity translation is trivial on a modal type.
def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

def Br_♭ (A :♭| Type) (a :♭| A) : Br (♭ A) (flat. a) (flat. a) ≔ flat. a

def Br_♭_trivial (A :♭| Type) (a₀ a₁ : ♭ A) (a₂ : Br (♭ A) a₀ a₁)
  : eq (♭ A) a₀ a₁
  ≔ match a₂ [ flat. x ⤇ rfl. ]

def eqd (A : Type) (a₀ a₁ : A) (a₂ : eq A a₀ a₁) (B : A → Type) (b₀ : B a₀)
  (b₁ : B a₁)
  : Type
  ≔ match a₂ [ rfl. ↦ eq (B a₀) b₀ b₁ ]

def Br_♭_trivial2 (A :♭| Type) (a₀ a₁ : ♭ A) (a₂ : Br (♭ A) a₀ a₁)
  : eqd (♭ A) a₀ a₁ (Br_♭_trivial A a₀ a₁ a₂) (a ↦ Br (♭ A) a₀ a) (rel a₀)
      a₂
  ≔ match a₂ [ flat. a ⤇ rfl. ]
