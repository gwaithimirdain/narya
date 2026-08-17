def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]

def Nat : Type ≔ ?

solve 0 ≔ ℕ

def plus (x y : ℕ) : ℕ ≔ ?

solve 1 ≔ match y [ zero. ↦ ? | suc. z ↦ ? ]

solve 2 ≔ x

solve 3 ≔ suc. (plus x z)

echo plus 4 5

{` holes can refer to global metas and depend on the value of previously filled holes `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def 𝔹 : Type ≔ data [ false. | true. ]

def Jd (A : Type) (a : A) : A → Type ≔ data [ rfl. : Jd A a a ]

def invol1 : Σ (𝔹 → 𝔹) (f ↦ (x : 𝔹) → Jd 𝔹 x (f (f x))) ≔
  let not : 𝔹 → 𝔹 ≔ [ false. ↦ true. | true. ↦ false. ] in
  (?, ?)

solve 4 ≔ not

solve 5 ≔ [ true. ↦ rfl. | false. ↦ rfl. ]

{` holes can create global metas `}

def invol2 : Σ (𝔹 → 𝔹) (f ↦ (x : 𝔹) → Jd 𝔹 x (f (f x))) ≔ ?

solve 6 ≔ let not : 𝔹 → 𝔹 ≔ [ false. ↦ true. | true. ↦ false. ] in (not, ?)

solve 7 ≔ [ true. ↦ rfl. | false. ↦ rfl. ]

{` the displayed context and type of a hole are updated when the holes they depend on are solved `}

def El (X : Type) : Type ≔ X

{` here the type of the second hole is the first hole, and the type of the third is a variable whose type is the first hole `}

def dep : Σ Type (X ↦ Σ X (_ ↦ X → 𝔹)) ≔ (El ?, (?, x ↦ ?))

show hole 9

show hole 10

solve 8 ≔ 𝔹

show hole 9

show hole 10

solve 9 ≔ true.

solve 10 ≔ x

{` the same happens for a dependency through the constant currently being defined `}

def dep' : Σ Type (X ↦ X) ≔ (?, ?)

show hole 12

solve 11 ≔ 𝔹

show hole 12

solve 12 ≔ false.
