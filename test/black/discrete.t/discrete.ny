{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

` The modality ♭ is a *discrete* comonad: working under a ♭ lock filters
` out the parametric dimensions.  We set up the usual comonad structure, plus a
` non-modal type family T for contrast with the modal family ♭T.

def f (A :♭| Type) (x :♭| A) : A ≔ x

def ♭T (A :♭| Type) : Type ≔ data [ box. (x :♭| A) ]

def ♭map (A B :♭| Type) (g :♭| A → B) : ♭T A → ♭T B ≔ [
| box. x ↦ box. (g x)]

def ε (A :♭| Type) (u : ♭T A) : A ≔ match u [ box. x ↦ x ]

def △ (A :♭| Type) (u : ♭T A) : ♭T (♭T A) ≔ match u [
| box. x ↦ box. (box. x)]

` A non-modal family, whose refl has an unfiltered (square) domain.
def T (A : Type) : Type ≔ data [ mk. (x : A) ]

` The parametricity translation is trivial on a modal type.
def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

def Br_♭T (A :♭| Type) (a :♭| A) : Br (♭T A) (box. a) (box. a) ≔ box. a

def Br_♭T_trivial (A :♭| Type) (a₀ a₁ : ♭T A) (a₂ : Br (♭T A) a₀ a₁)
  : eq (♭T A) a₀ a₁
  ≔ match a₂ [ box. a ⤇ rfl. ]

def eqd (A : Type) (a₀ a₁ : A) (a₂ : eq A a₀ a₁) (B : A → Type) (b₀ : B a₀)
  (b₁ : B a₁)
  : Type
  ≔ match a₂ [ rfl. ↦ eq (B a₀) b₀ b₁ ]

def Br_♭T_trivial2 (A :♭| Type) (a₀ a₁ : ♭T A) (a₂ : Br (♭T A) a₀ a₁)
  : eqd (♭T A) a₀ a₁ (Br_♭T_trivial A a₀ a₁ a₂) (a ↦ Br (♭T A) a₀ a)
      (rel a₀) a₂
  ≔ match a₂ [ box. a ⤇ rfl. ]
