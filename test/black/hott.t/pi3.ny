{` Transport and lifting compute on 3-dimensional Π-types `}

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

axiom f000 : (x000 : A000) → B000 x000

axiom f001 : (x001 : A001) → B001 x001

axiom f010 : (x010 : A010) → B010 x010

axiom f011 : (x011 : A011) → B011 x011

axiom f100 : (x100 : A100) → B100 x100

axiom f101 : (x101 : A101) → B101 x101

axiom f110 : (x110 : A110) → B110 x110

axiom f111 : (x111 : A111) → B111 x111

axiom f002
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A002 B002
      f000 f001

axiom f012
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A012 B012
      f010 f011

axiom f020
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A020 B020
      f000 f010

axiom f021
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A021 B021
      f001 f011

axiom f102
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A102 B102
      f100 f101

axiom f112
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A112 B112
      f110 f111

axiom f120
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A120 B120
      f100 f110

axiom f121
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A121 B121
      f101 f111

axiom f200
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A200 B200
      f000 f100

axiom f201
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A201 B201
      f001 f101

axiom f210
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A210 B210
      f010 f110

axiom f211
  : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A211 B211
      f011 f111

axiom f022
  : ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉ⁾ A022 B022
      f002 f012 f020 f021

axiom f122
  : ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉ⁾ A122 B122
      f102 f112 f120 f121

axiom f202
  : ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉ⁾ A202 B202
      f002 f102 f200 f201

axiom f212
  : ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉ⁾ A212 B212
      f012 f112 f210 f211

axiom f220
  : ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉ⁾ A220 B220
      f020 f120 f200 f210

axiom f221
  : ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉ⁾ A221 B221
      f021 f121 f201 f211

axiom a000 : A000

axiom a001 : A001

axiom a010 : A010

axiom a011 : A011

axiom a100 : A100

axiom a101 : A101

axiom a110 : A110

axiom a111 : A111

axiom a002 : A002 a000 a001

axiom a012 : A012 a010 a011

axiom a020 : A020 a000 a010

axiom a021 : A021 a001 a011

axiom a102 : A102 a100 a101

axiom a112 : A112 a110 a111

axiom a120 : A120 a100 a110

axiom a121 : A121 a101 a111

axiom a200 : A200 a000 a100

axiom a201 : A201 a001 a101

axiom a210 : A210 a010 a110

axiom a211 : A211 a011 a111

axiom a022 : A022 a002 a012 a020 a021

axiom a122 : A122 a102 a112 a120 a121

axiom a202 : A202 a002 a102 a200 a201

axiom a212 : A212 a012 a112 a210 a211

axiom a220 : A220 a020 a120 a200 a210

axiom a221 : A221 a021 a121 a201 a211

axiom a222 : A222 a022 a122 a202 a212 a220 a221

{` 1-box-filling acting on 2-dimensional functions `}
echo ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉᵉ⁾ A222
         B222 f022 f122 f202 f212
  .trr.1 f220 a221

def Πtrr
  : Id (B221 a221 (f021 a021) (f121 a121) (f201 a201) (f211 a211))
      (((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉᵉ⁾ A222
           B222 f022 f122 f202 f212
       .trr.1 f220 a221)
      (B222
           (A222 (A022 (A002 .liftl a001) (A012 .liftl a011) .liftl a021)
                (A122 (A102 .liftl a101) (A112 .liftl a111) .liftl a121)
                (A202 (A002 .liftl a001) (A102 .liftl a101) .liftl a201)
                (A212 (A012 .liftl a011) (A112 .liftl a111) .liftl a211)
            .liftl a221)
           (f022 (A022 (A002 .liftl a001) (A012 .liftl a011) .liftl a021))
           (f122 (A122 (A102 .liftl a101) (A112 .liftl a111) .liftl a121))
           (f202 (A202 (A002 .liftl a001) (A102 .liftl a101) .liftl a201))
           (f212 (A212 (A012 .liftl a011) (A112 .liftl a111) .liftl a211))
       .trr.1
         (f220
            (A222 (A022 (A002 .liftl a001) (A012 .liftl a011) .liftl a021)
                 (A122 (A102 .liftl a101) (A112 .liftl a111) .liftl a121)
                 (A202 (A002 .liftl a001) (A102 .liftl a101) .liftl a201)
                 (A212 (A012 .liftl a011) (A112 .liftl a111) .liftl a211)
             .trl.1 a221)))
  ≔ refl _

{` And in the other direction `}
echo ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉᵉ⁾ A222
         B222 f022 f122 f202 f212
  .trl.1 f221 a220

def Πtrl
  : Id (B220 a220 (f020 a020) (f120 a120) (f200 a200) (f210 a210))
      (((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉᵉ⁾ A222
           B222 f022 f122 f202 f212
       .trl.1 f221 a220)
      (B222
           (A222 (A022 (A002 .liftr a000) (A012 .liftr a010) .liftr a020)
                (A122 (A102 .liftr a100) (A112 .liftr a110) .liftr a120)
                (A202 (A002 .liftr a000) (A102 .liftr a100) .liftr a200)
                (A212 (A012 .liftr a010) (A112 .liftr a110) .liftr a210)
            .liftr a220)
           (f022 (A022 (A002 .liftr a000) (A012 .liftr a010) .liftr a020))
           (f122 (A122 (A102 .liftr a100) (A112 .liftr a110) .liftr a120))
           (f202 (A202 (A002 .liftr a000) (A102 .liftr a100) .liftr a200))
           (f212 (A212 (A012 .liftr a010) (A112 .liftr a110) .liftr a210))
       .trl.1
         (f221
            (A222 (A022 (A002 .liftr a000) (A012 .liftr a010) .liftr a020)
                 (A122 (A102 .liftr a100) (A112 .liftr a110) .liftr a120)
                 (A202 (A002 .liftr a000) (A102 .liftr a100) .liftr a200)
                 (A212 (A012 .liftr a010) (A112 .liftr a110) .liftr a210)
             .trr.1 a220)))
  ≔ refl _
