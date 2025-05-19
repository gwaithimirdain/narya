{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

{` Transport and lifting compute on Σ-types `}

option function boundaries ≔ implicit
option type boundaries ≔ implicit

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

axiom A₀ : Type
axiom A₁ : Type
axiom A₂ : Id Type A₀ A₁
axiom B₀ : A₀ → Type
axiom B₁ : A₁ → Type
axiom B₂ : Id ((X ↦ X → Type) : Type → Type) A₂ B₀ B₁

axiom u₀ : Σ A₀ B₀

echo refl Σ A₂ B₂ .trr u₀
echo refl Σ A₂ B₂ .trr u₀ .fst
echo A₂ .trr.1 (u₀ .fst)

def Σtrrfst : Id A₁ (refl Σ A₂ B₂ .trr u₀ .fst) (A₂ .trr.1 (u₀ .fst))
  ≔ refl (A₂ .trr.1 (u₀ .fst))

echo refl Σ A₂ B₂ .trr u₀ .snd
echo B₂ (A₂ .liftr.1 (u₀ .fst)) .trr.1 (u₀ .snd)

def Σtrrsnd
  : Id (B₁ (A₂ .trr.1 (u₀ .fst))) (refl Σ A₂ B₂ .trr u₀ .snd)
      (B₂ (A₂ .liftr.1 (u₀ .fst)) .trr.1 (u₀ .snd))
  ≔ refl (B₂ (A₂ .liftr.1 (u₀ .fst)) .trr.1 (u₀ .snd))

def Σtrr
  : Id (Σ A₁ B₁) (refl Σ A₂ B₂ .trr u₀)
      (A₂ .trr.1 (u₀ .fst), B₂ (A₂ .liftr.1 (u₀ .fst)) .trr.1 (u₀ .snd))
  ≔ refl (refl Σ A₂ B₂ .trr u₀)

echo refl Σ A₂ B₂ .liftr u₀
echo refl Σ A₂ B₂ .liftr u₀ .fst
echo A₂ .liftr.1 (u₀ .fst)
echo refl Σ A₂ B₂ .liftr u₀ .snd

echo B₂ (A₂ .liftr.1 (u₀ .fst)) .liftr.1 (u₀ .snd)

def Σliftr
  : Id (refl Σ A₂ B₂ u₀ (refl Σ A₂ B₂ .trr.1 u₀)) (refl Σ A₂ B₂ .liftr u₀)
      (A₂ .liftr.1 (u₀ .fst), B₂ (A₂ .liftr.1 (u₀ .fst)) .liftr.1 (u₀ .snd))
  ≔ refl (refl Σ A₂ B₂ .liftr u₀)

axiom u₁ : Σ A₁ B₁

echo refl Σ A₂ B₂ .trl u₁
echo refl Σ A₂ B₂ .trl u₁ .fst
echo refl Σ A₂ B₂ .trl u₁ .snd

def Σtrl
  : Id (Σ A₀ B₀) (refl Σ A₂ B₂ .trl u₁)
      (A₂ .trl.1 (u₁ .fst), B₂ (A₂ .liftl.1 (u₁ .fst)) .trl.1 (u₁ .snd))
  ≔ refl (refl Σ A₂ B₂ .trl u₁)

echo refl Σ A₂ B₂ .liftl u₁
echo refl Σ A₂ B₂ .liftl u₁ .fst
echo refl Σ A₂ B₂ .liftl u₁ .snd

def Σliftl
  : Id (refl Σ A₂ B₂ (refl Σ A₂ B₂ .trl.1 u₁) u₁) (refl Σ A₂ B₂ .liftl u₁)
      (A₂ .liftl.1 (u₁ .fst), B₂ (A₂ .liftl.1 (u₁ .fst)) .liftl.1 (u₁ .snd))
  ≔ refl (refl Σ A₂ B₂ .liftl u₁)
