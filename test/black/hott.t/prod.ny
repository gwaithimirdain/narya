{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

{` Transport and lifting compute on product types `}

def prod (A : Type) (B : Type) : Type ≔ sig ( fst : A, snd : B )

axiom A₀ : Type
axiom A₁ : Type
axiom A₂ : Id Type A₀ A₁
axiom B₀ : Type
axiom B₁ : Type
axiom B₂ : Id Type B₀ B₁

axiom u₀ : prod A₀ B₀

echo refl prod A₂ B₂ .trr u₀
echo refl prod A₂ B₂ .trr u₀ .fst
echo refl prod A₂ B₂ .trr u₀ .snd

echo refl prod A₂ B₂ .liftr u₀
echo refl prod A₂ B₂ .liftr u₀ .fst
echo refl prod A₂ B₂ .liftr u₀ .snd
