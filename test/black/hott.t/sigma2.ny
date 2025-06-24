{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

{` Transport and liftnig compute in 2-dimensional Σ-types `}

axiom A00 : Type

axiom A01 : Type

axiom A02 : Id Type A00 A01

axiom A10 : Type

axiom A11 : Type

axiom A12 : Id Type A10 A11

axiom A20 : Id Type A00 A10

axiom A21 : Id Type A01 A11

axiom A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21

axiom B00 : A00 → Type

axiom B01 : A01 → Type

axiom B02 : Id ((X ↦ X → Type) : Type → Type) (A02) B00 B01

axiom B10 : A10 → Type

axiom B11 : A11 → Type

axiom B12 : Id ((X ↦ X → Type) : Type → Type) (A12) B10 B11

axiom B20 : Id ((X ↦ X → Type) : Type → Type) (A20) B00 B10

axiom B21 : Id ((X ↦ X → Type) : Type → Type) (A21) B01 B11

axiom B22 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ (A22) B02 B12 B20 B21

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

axiom u00 : Σ A00 B00

axiom u01 : Σ A01 B01

axiom u02 : Id Σ A02 B02 u00 u01

axiom u10 : Σ A10 B10

axiom u11 : Σ A11 B11

axiom u12 : Id Σ A12 B12 u10 u11

axiom u20 : Id Σ A20 B20 u00 u10

axiom u21 : Id Σ A21 B21 u01 u11

{` Uniform operations `}
echo Σ⁽ᵉᵉ⁾ A22 B22 .trr.1 u02 .fst

echo Σ⁽ᵉᵉ⁾ A22 B22 .trr.2 u20 .fst

{` Non-uniform operations, box-filling `}
synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trr u20

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trr u20 .fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trr u20 .snd

def Σtrr
  : Id (refl Σ A21 B21 u01 u11) (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trr u20)
      (A22 (u02 .fst) (u12 .fst) .trr.1 (u20 .fst),
       B22 (A22 (u02 .fst) (u12 .fst) .liftr.1 (u20 .fst)) (u02 .snd)
           (u12 .snd)
         .trr.1 (u20 .snd))
  ≔ refl _

synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftr u20

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftr u20 .fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftr u20 .snd

def Σliftr
  : Id (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 u20 (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trr.1 u20))
      (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftr u20)
      (A22 (u02 .fst) (u12 .fst) .liftr.1 (u20 .fst),
       B22 (A22 (u02 .fst) (u12 .fst) .liftr.1 (u20 .fst)) (u02 .snd)
           (u12 .snd)
         .liftr.1 (u20 .snd))
  ≔ refl _

synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trl u21

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trl u21 .fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trl u21 .snd

def Σtrl
  : Id (refl Σ A20 B20 u00 u10) (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trl u21)
      (A22 (u02 .fst) (u12 .fst) .trl.1 (u21 .fst),
       B22 (A22 (u02 .fst) (u12 .fst) .liftl.1 (u21 .fst)) (u02 .snd)
           (u12 .snd)
         .trl.1 (u21 .snd))
  ≔ refl _

synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftl u21

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftl u21 .fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftl u21 .snd

def Σliftl
  : Id (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trl.1 u21) u21)
      (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftl u21)
      (A22 (u02 .fst) (u12 .fst) .liftl.1 (u21 .fst),
       B22 (A22 (u02 .fst) (u12 .fst) .liftl.1 (u21 .fst)) (u02 .snd)
           (u12 .snd)
         .liftl.1 (u21 .snd))
  ≔ refl _
