{` Transport and lifting compute on 3-dimensional Σ-types `}

axiom A000 : Type

axiom A001 : Type

axiom A010 : Type

axiom A011 : Type

axiom A100 : Type

axiom A101 : Type

axiom A110 : Type

axiom A111 : Type

axiom A002 : Id Type A000 A001

axiom A012 : Id Type A010 A011

axiom A020 : Id Type A000 A010

axiom A021 : Id Type A001 A011

axiom A102 : Id Type A100 A101

axiom A112 : Id Type A110 A111

axiom A120 : Id Type A100 A110

axiom A121 : Id Type A101 A111

axiom A200 : Id Type A000 A100

axiom A201 : Id Type A001 A101

axiom A210 : Id Type A010 A110

axiom A211 : Id Type A011 A111

axiom A022 : Type⁽ᵉᵉ⁾ A002 A012 A020 A021

axiom A122 : Type⁽ᵉᵉ⁾ A102 A112 A120 A121

axiom A202 : Type⁽ᵉᵉ⁾ A002 A102 A200 A201

axiom A212 : Type⁽ᵉᵉ⁾ A012 A112 A210 A211

axiom A220 : Type⁽ᵉᵉ⁾ A020 A120 A200 A210

axiom A221 : Type⁽ᵉᵉ⁾ A021 A121 A201 A211

axiom A222 : Type⁽ᵉᵉᵉ⁾ A022 A122 A202 A212 A220 A221

axiom B000 : A000 → Type

axiom B001 : A001 → Type

axiom B010 : A010 → Type

axiom B011 : A011 → Type

axiom B100 : A100 → Type

axiom B101 : A101 → Type

axiom B110 : A110 → Type

axiom B111 : A111 → Type

axiom B002 : Id ((X ↦ X → Type) : Type → Type) A002 B000 B001

axiom B012 : Id ((X ↦ X → Type) : Type → Type) A012 B010 B011

axiom B020 : Id ((X ↦ X → Type) : Type → Type) A020 B000 B010

axiom B021 : Id ((X ↦ X → Type) : Type → Type) A021 B001 B011

axiom B102 : Id ((X ↦ X → Type) : Type → Type) A102 B100 B101

axiom B112 : Id ((X ↦ X → Type) : Type → Type) A112 B110 B111

axiom B120 : Id ((X ↦ X → Type) : Type → Type) A120 B100 B110

axiom B121 : Id ((X ↦ X → Type) : Type → Type) A121 B101 B111

axiom B200 : Id ((X ↦ X → Type) : Type → Type) A200 B000 B100

axiom B201 : Id ((X ↦ X → Type) : Type → Type) A201 B001 B101

axiom B210 : Id ((X ↦ X → Type) : Type → Type) A210 B010 B110

axiom B211 : Id ((X ↦ X → Type) : Type → Type) A211 B011 B111

axiom B022 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ A022 B002 B012 B020 B021

axiom B122 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ A122 B102 B112 B120 B121

axiom B202 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ A202 B002 B102 B200 B201

axiom B212 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ A212 B012 B112 B210 B211

axiom B220 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ A220 B020 B120 B200 B210

axiom B221 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ A221 B021 B121 B201 B211

axiom B222
  : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉᵉ⁾ A222 B022 B122 B202 B212 B220 B221

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

axiom u000 : Σ A000 B000

axiom u001 : Σ A001 B001

axiom u010 : Σ A010 B010

axiom u011 : Σ A011 B011

axiom u100 : Σ A100 B100

axiom u101 : Σ A101 B101

axiom u110 : Σ A110 B110

axiom u111 : Σ A111 B111

axiom u002 : Id Σ A002 B002 u000 u001

axiom u012 : Id Σ A012 B012 u010 u011

axiom u020 : Id Σ A020 B020 u000 u010

axiom u021 : Id Σ A021 B021 u001 u011

axiom u102 : Id Σ A102 B102 u100 u101

axiom u112 : Id Σ A112 B112 u110 u111

axiom u120 : Id Σ A120 B120 u100 u110

axiom u121 : Id Σ A121 B121 u101 u111

axiom u200 : Id Σ A200 B200 u000 u100

axiom u201 : Id Σ A201 B201 u001 u101

axiom u210 : Id Σ A210 B210 u010 u110

axiom u211 : Id Σ A211 B211 u011 u111

axiom u022 : Σ⁽ᵉᵉ⁾ A022 B022 u002 u012 u020 u021

axiom u122 : Σ⁽ᵉᵉ⁾ A122 B122 u102 u112 u120 u121

axiom u202 : Σ⁽ᵉᵉ⁾ A202 B202 u002 u102 u200 u201

axiom u212 : Σ⁽ᵉᵉ⁾ A212 B212 u012 u112 u210 u211

axiom u220 : Σ⁽ᵉᵉ⁾ A220 B220 u020 u120 u200 u210

axiom u221 : Σ⁽ᵉᵉ⁾ A221 B221 u021 u121 u201 u211

{` Non-uniform operations, box-filling `}
synth Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trr u220

echo Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trr u220 .fst

echo Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trr u220 .snd

def Σtrr
  : Id (Σ⁽ᵉᵉ⁾ A221 B221 u021 u121 u201 u211)
      (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trr u220)
      (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
         .trr (u220 .fst),
       B222
           (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
            .liftr (u220 .fst)) (u022 .snd) (u122 .snd) (u202 .snd)
           (u212 .snd)
         .trr (u220 .snd))
  ≔ refl _

synth Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .liftr u220

def Σliftr
  : Id
      (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 u220
         (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trr u220))
      (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .liftr u220)
      (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
         .liftr (u220 .fst),
       B222
           (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
            .liftr (u220 .fst)) (u022 .snd) (u122 .snd) (u202 .snd)
           (u212 .snd)
         .liftr (u220 .snd))
  ≔ refl _

synth Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trl u221

def Σtrl
  : Id (Σ⁽ᵉᵉ⁾ A220 B220 u020 u120 u200 u210)
      (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trl u221)
      (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
         .trl (u221 .fst),
       B222
           (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
            .liftl (u221 .fst)) (u022 .snd) (u122 .snd) (u202 .snd)
           (u212 .snd)
         .trl (u221 .snd))
  ≔ refl _

synth Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .liftl u221

def Σliftl
  : Id
      (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212
         (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .trl u221) u221)
      (Σ⁽ᵉᵉᵉ⁾ A222 B222 u022 u122 u202 u212 .liftl u221)
      (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
         .liftl (u221 .fst),
       B222
           (A222 (u022 .fst) (u122 .fst) (u202 .fst) (u212 .fst)
            .liftl (u221 .fst)) (u022 .snd) (u122 .snd) (u202 .snd)
           (u212 .snd)
         .liftl (u221 .snd))
  ≔ refl _
