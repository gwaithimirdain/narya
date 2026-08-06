{` -*- narya-prog-args: ("-proofgeneral" "-dtt") -*- `}

{` Places that other-axis degeneracies like ⁽ᵈ¹⁾ currently lead to symmetries: `}

def Gel (A : Type) (B : A → Type) : Type⁽ᵈ⁾ A ≔ sig a ↦ ( ungel : B a )
axiom A : Type
axiom B : A → Type
axiom a : A
axiom b : B a
echo ((ungel ≔ b) : Gel A B a)⁽ᵈ¹⁾

{`
sym (ungel ≔ b⁽ᵈ⁾)
  : sym (Gel⁽ᵈ⁾ A⁽ᵈ⁾ B⁽ᵈ⁾) {a} (ungel ≔ b) a⁽ᵈ⁾
 `}

axiom C : Type
axiom c : C
axiom f : A → C⁽ᵈ⁾ c
echo (f a)⁽ᵈ¹⁾

{`
sym (f⁽ᵈ⁾ a⁽ᵈ⁾)
  : C⁽ᵈᵈ⁾ (f a) c⁽ᵈ⁾
 `}

{` In the above cases, we could imagine keeping the whole other-axis degeneracy on the outside rather than pushing part of it through.  However, with abstractions we have a bigger problem: `}

axiom A : Type
axiom B : Type
axiom f : A → B
axiom g : (a : A) (b : A⁽ᵈ⁾ a) → B⁽ᵈ⁾ (f a)
def h : {a : A} (b : A⁽ᵈ⁾ a) →⁽ᵈ⁾ B⁽ᵈ⁾ (f a) ≔ {a} b ↦ g a b
synth h⁽ᵈ¹⁾

{`
h⁽ᵈ¹⁾
  : {b₀₀ : A} {b₀₁ : A⁽ᵈ⁾ b₀₀} {b₁₀ : A⁽ᵈ⁾ b₀₀} (b₁₁ : A⁽ᵈᵈ⁾ b₀₁ b₁₀)
    →⁽ᵈᵈ⁾ B⁽ᵈᵈ⁾ (g b₀₀ b₀₁) (f⁽ᵈ⁾ b₁₀)
 `}

axiom a₀₀ : A
axiom a₀₁ : A⁽ᵈ⁾ a₀₀
axiom a₁₀ : A⁽ᵈ⁾ a₀₀
axiom a₁₁ : A⁽ᵈᵈ⁾ a₀₁ a₁₀

echo h⁽ᵈ¹⁾ {a₀₀} {a₀₁} {a₁₀} a₁₁

{`
sym (g⁽ᵈ⁾ a₁₀ (sym a₁₁))
  : B⁽ᵈᵈ⁾ (g a₀₀ a₀₁) (f⁽ᵈ⁾ a₁₀)
 `}

{` Here h is defined as a lambda-abstraction to be essentially g, and we're applying (a degenerate version of) it to exactly as many arguments as it needs.  If anything like ordinary normalization is going to hold, h⁽ᵈ¹⁾ {a₀₀} {a₀₁} {a₁₀} a₁₁ can't be stuck: it must reduce to something, and clearly that something must involve g somehow, and about the only conceivable way for it to use g is via g⁽ᵈ⁾.  But `}

synth g⁽ᵈ⁾

{` g⁽ᵈ⁾
  : {a₀ : A} (a₁ : A⁽ᵈ⁾ a₀) {b₀ : A⁽ᵈ⁾ a₀} (b₁ : A⁽ᵈᵈ⁾ a₁ b₀)
    →⁽ᵈ⁾ B⁽ᵈᵈ⁾ (f⁽ᵈ⁾ a₁) (g a₀ b₀)
 `}

{` has its output dependencies in the other order than h⁽ᵈ¹⁾.  I don't see any way to avoid a symmetry here. `}
