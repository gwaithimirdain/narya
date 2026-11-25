{` -*- narya-prog-args: ("-proofgeneral" "-discrete-adjunction" "-parametric" "-external" "-direction" "p,rel,Br") -*- `}

def △ (A :△| Disc) : Type ≔ data [ △. (_ :△| A) ]

def □ (A :□| Type) : Disc ≔ sig ( (_ :△| _) .□ : A )

def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

{` △ is discrete. `}

def Br_△ (A :△| Disc) (a :△| A) : Br (△ A) (△. a) (△. a) ≔ △. a

def Br_to_eq (A :△| Disc) (a₀ a₁ : △ A) (a₂ : Br (△ A) a₀ a₁)
  : eq (△ A) a₀ a₁
  ≔ match a₂ [ △. a ⤇ rfl. ]

{` The match on a0 may look unnecessary, since we decompose it into [△. a] and then immediately use it again as [△. a].  But we can't write just [rel a0] because [a0] is not accessible in a △□-locked context.  If we decompose it, then [a] is △-annotated, hence usable in the △□△-locked context that we get inside [△.] since there is a unit 2-cell △ ⇒ △□△. `}
def eq_to_Br (A :△| Disc) (a0 a1 : △ A) (a2 : eq (△ A) a0 a1)
  : Br (△ A) a0 a1
  ≔ match a2 [ rfl. ↦ match a0 [ △. a ↦ rel (△. a : △ A) ] ]

def eq_to_Br_to_eq (A :△| Disc) (a₀ a₁ : △ A) (a₂ : Br (△ A) a₀ a₁)
  : eq (Br (△ A) a₀ a₁) a₂ (eq_to_Br A a₀ a₁ (Br_to_eq A a₀ a₁ a₂))
  ≔ match a₂ [ △. a ⤇ rfl. ]

def Br_to_eq_to_Br (A :△| Disc) (a₀ a₁ : △ A) (a₂ : eq (△ A) a₀ a₁)
  : eq (eq (△ A) a₀ a₁) a₂ (Br_to_eq A a₀ a₁ (eq_to_Br A a₀ a₁ a₂))
  ≔ match a₂ [ rfl. ↦ match a₀ [ △. 𝑥 ↦ rfl. ] ]
