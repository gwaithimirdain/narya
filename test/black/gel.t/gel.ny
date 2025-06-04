def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ (
  ungel : R a b )

axiom A : Type
axiom B : Type
axiom R : A → B → Type
axiom a₀ : A
axiom a₁ : A
axiom a₂ : Id A a₀ a₁ 
axiom b₀ : B
axiom b₁ : B
axiom b₂ : Id B b₀ b₁
axiom r₀ : R a₀ b₀
axiom r₁ : R a₁ b₁

{` An intrinsic symmetry of a higher-dimensional Gel is no longer a record type `}
axiom M : (Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂
echo sym M
{` But its terms can be symmetrized to end up in a record type `}
echo sym M .ungel

{` And it satisfies an eta-rule inherited from that record type `}
def eta
  : Id ((Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂) M
      (sym (ungel ≔ sym M .ungel))
  ≔ refl M

{` refl of Gel builds a square of correspondences`}
axiom A0 : Type
axiom B0 : Type
axiom R0 : A0 → B0 → Type
axiom A1 : Type
axiom B1 : Type
axiom R1 : A1 → B1 → Type
axiom A2 : Id Type A0 A1
axiom B2 : Id Type B0 B1
axiom R2
  : refl ((X ↦ Y ↦ (X → Y → Type)) : Type → Type → Type) A0 A1 A2 B0 B1 B2 R0
      R1

def r_gelr2 ≔ refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2

synth r_gelr2
{`r_gelr2 : Type⁽ᵉᵉ⁾ A0 A1 A2 B0 B1 B2 (Gel A0 B0 R0) (Gel A1 B1 R1)`}

{`We can apply it to some points.`}
axiom a0 : A0
axiom a1 : A1
axiom a2 : A2 a0 a1
axiom b0 : B0
axiom b1 : B1
axiom b2 : B2 b0 b1
axiom r0 : R0 a0 b0
axiom r1 : R1 a1 b1

def r2ty ≔ r_gelr2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0) (ungel ≔ r1)

axiom r2 : r2ty
{`Since this is a square in UU, we can symmetrize it. `}

def r_sym_gelr2 ≔ sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2)

synth r_sym_gelr2
{`r_sym_gelr2 : Type⁽ᵉᵉ⁾ A0 B0 (Gel A0 B0 R0) A1 B1 (Gel A1 B1 R1) A2 B2`}

{`This doesn't compute to anything: the symmetry is "stuck" as an insertion outside the Gel.  In particular, it is a different type (see the comments below two synth commands above), which can be applied to the same points in transposed order.`}

def sym_r2ty ≔ r_sym_gelr2 a0 b0 (ungel ≔ r0) a1 b1 (ungel ≔ r1) a2 b2

axiom r2' : sym_r2ty

{`However, it is *isomorphic* to the original double span, by symmetry again.`}

echo (sym r2 : sym_r2ty)
echo (sym r2' : r2ty)

def symsym_r2 ≔ sym (sym r2)

def symsym_r2_eq_r2 : Id r2ty symsym_r2 r2 ≔ refl r2

def symsym_r2' ≔ sym (sym r2')

def symsym_r2'_eq_r2' : Id r2ty symsym_r2 r2 ≔ refl r2
