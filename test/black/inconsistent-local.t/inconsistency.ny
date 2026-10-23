{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-inconsistent-local") -*- `}

def ∇ (A :∇| Disc) : Type ≔ sig ( (_ :□| _) .∇ : A )

def Br∇ (A :∇| Disc) (u v : ∇ A) : Br (∇ A) u v ≔ ()

def ∇′ (A :∇| Disc) : Type ≔ data [ ∇. (_ :∇| A) ]

def ∇_to_∇′ (A :∇| Disc) (u : ∇ A) : ∇′ A ≔ ∇. ((u :□| _) .∇)

def ∇′_to_∇ (A :∇| Disc) (u : ∇′ A) : ∇ A ≔ match u [
| ∇. x ↦ (∇ ≔ x)]

def eq (B : Type) (b : B) : B → Type ≔ data [ rfl. : eq B b b ]

def eq_of_Br∇′ (A :∇| Disc) (u₀ u₁ : ∇′ A) (u₂ : Br (∇′ A) u₀ u₁)
  : eq (∇′ A) u₀ u₁
  ≔ match u₂ [ ∇. 𝑥 ⤇ rfl. ]

def 𝔹 : Disc ≔ data [ true. | false. ]

def ∅ : Disc ≔ data []

def ⊤ : Disc ≔ sig ()

def eqD (B : Disc) (b : B) : B → Disc ≔ data [ rfl. : eqD B b b ]

def trD (B : Disc) (P : B → Disc) (b₀ b₁ : B) (b₂ : eqD B b₀ b₁)
  : P b₀ → P b₁
  ≔ match b₂ [ rfl. ↦ x ↦ x ]

def true≠false (u : eqD 𝔹 true. false.) : ∅ ≔
  let code : 𝔹 → Disc ≔ [ true. ↦ ⊤ | false. ↦ ∅ ] in
  trD 𝔹 code true. false. u ()

def ap (A B : Type) (f : A → B) (a₀ a₁ : A) (a₂ : eq A a₀ a₁)
  : eq B (f a₀) (f a₁)
  ≔ match a₂ [ rfl. ↦ rfl. ]

def ∇true : ∇ 𝔹 ≔ (true.,)

def ∇false : ∇ 𝔹 ≔ (false.,)

def ∇′true : ∇′ 𝔹 ≔ ∇. true.

def ∇′false : ∇′ 𝔹 ≔ ∇. false.

def ∇′true＝∇′false : eq (∇′ 𝔹) ∇′true ∇′false
  ≔ eq_of_Br∇′ 𝔹 ∇′true ∇′false (rel (∇_to_∇′ 𝔹) (Br∇ 𝔹 ∇true ∇false))

def ∇′eqD_of_eq (B :∇| Disc) (u₀ u₁ : ∇′ B) (u₂ : eq (∇′ B) u₀ u₁)
  : match u₀, u₁ [ ∇. x₀, ∇. x₁ ↦ ∇′ (eqD B x₀ x₁) ]
  ≔ match u₂ [ rfl. ↦ match u₀ [ ∇. 𝑥 ↦ ∇. rfl. ] ]

def ∇′oops : ∇′ ∅
  ≔ match ∇′eqD_of_eq 𝔹 (∇. true.) (∇. false.) ∇′true＝∇′false [
| ∇. e ↦ ∇. (true≠false e)]

def oopsD : ∅ ≔ match (∇′oops :□| _) [ ∇. e ↦ e ]

def ⊘ : Type ≔ data []

def oops : ⊘ ≔ match (oopsD :△| _) [ ]

synth oops
