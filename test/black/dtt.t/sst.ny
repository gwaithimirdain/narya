{` -*- narya-prog-args: ("-proofgeneral" "-dtt") -*- `}

{` Unary Gel-types `}
def Gel (A : Type) (A' : A → Type) : Type⁽ᵈ⁾ A ≔ sig x ↦ ( ungel : A' x )

{` The definition of semi-simplicial types `}
def SST : Type ≔ codata [ X .z : Type | X .s : (X .z) → SST⁽ᵈ⁾ X ]

` Extracting some low-dimensional simplices
def 0s (X : SST) : Type ≔ X .z

def 1s (X : SST) (x₀ x₁ : 0s X) : Type ≔ X .s x₀ .z x₁

def 2s (X : SST) (x₀ x₁ : 0s X) (x₀₁ : 1s X x₀ x₁) (x₂ : 0s X)
  (x₀₂ : 1s X x₀ x₂) (x₁₂ : 1s X x₁ x₂)
  : Type
  ≔ X .s x₀ .s {x₁} x₀₁ .z {x₂} x₀₂ x₁₂

def 3s (X : SST) (x₀ x₁ : 0s X) (x₀₁ : 1s X x₀ x₁) (x₂ : 0s X)
  (x₀₂ : 1s X x₀ x₂) (x₁₂ : 1s X x₁ x₂) (x₀₁₂ : 2s X x₀ x₁ x₀₁ x₂ x₀₂ x₁₂)
  (x₃ : 0s X) (x₀₃ : 1s X x₀ x₃) (x₁₃ : 1s X x₁ x₃)
  (x₀₁₃ : 2s X x₀ x₁ x₀₁ x₃ x₀₃ x₁₃) (x₂₃ : 1s X x₂ x₃)
  (x₀₂₃ : 2s X x₀ x₂ x₀₂ x₃ x₀₃ x₂₃) (x₁₂₃ : 2s X x₁ x₂ x₁₂ x₃ x₁₃ x₂₃)
  : Type
  ≔ X
      .s x₀
      .s {x₁} x₀₁
      .s {x₂} {x₀₂} {x₁₂} x₀₁₂
      .z {x₃} {x₀₃} {x₁₃} x₀₁₃ {x₂₃} x₀₂₃ x₁₂₃

{` Singular SSTs, based on the Martin-Lof jdentity type for now. `}
def eq (A : Type) (x : A) : A → Type ≔ data [ rfl. : eq A x x ]

def Sing (A : Type) : SST ≔ [
| .z ↦ A
| .s ↦ x ↦ Sing⁽ᵈ⁾ (Gel A (y ↦ eq A x y))]

{` We normalize some low-dimensional simplex types of singular SSTs. `}
axiom A : Type

echo 0s (Sing A)

axiom a₀ : 0s (Sing A)

axiom a₁ : 0s (Sing A)

echo 1s (Sing A) a₀ a₁

axiom a₀₁ : 1s (Sing A) a₀ a₁

axiom a₂ : 0s (Sing A)

axiom a₀₂ : 1s (Sing A) a₀ a₂

axiom a₁₂ : 1s (Sing A) a₁ a₂

echo 2s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂

axiom a₀₁₂ : 2s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂

axiom a₃ : 0s (Sing A)

axiom a₀₃ : 1s (Sing A) a₀ a₃

axiom a₁₃ : 1s (Sing A) a₁ a₃

axiom a₀₁₃ : 2s (Sing A) a₀ a₁ a₀₁ a₃ a₀₃ a₁₃

axiom a₂₃ : 1s (Sing A) a₂ a₃

axiom a₀₂₃ : 2s (Sing A) a₀ a₂ a₀₂ a₃ a₀₃ a₂₃

axiom a₁₂₃ : 2s (Sing A) a₁ a₂ a₁₂ a₃ a₁₃ a₂₃

echo 3s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂ a₀₁₂ a₃ a₀₃ a₁₃ a₀₁₃ a₂₃ a₀₂₃ a₁₂₃

{` Every global type can be regarded as a "synthetic" augmented SST has a "fiber" over a point that is an (analytic) SST. `}
def sst.Fib (X :△□| Type) (x : X) : SST ≔ [
| .z ↦ X⁽ᵈ⁾ x
| .s ↦ y ↦ sst.Fib⁽ᵈ⁾ X y]

{` The empty SST `}
def sst.∅ : SST ≔ [ .z ↦ data [] | .s ↦ [ ] ]

{` The unit SST `}
def sst.𝟙 : SST ≔ [ .z ↦ sig () | .s ↦ _ ↦ sst.𝟙⁽ᵈ⁾ ]

{` Binary products of SSTs `}
def sst.prod (X Y : SST) : SST ≔ [
| .z ↦ sig (
    fst : X .z,
    snd : Y .z )
| .s ↦ xy ↦ sst.prod⁽ᵈ⁾ (X .s (xy .fst)) (Y .s (xy .snd))]

{` Dependent Σ-SSTs require symmetry! `}
def sst.Σ (X : SST) (Y : SST⁽ᵈ⁾ X) : SST ≔ [
| .z ↦ sig (
    fst : X .z,
    snd : Y .z fst )
| .s ↦ xy ↦ sst.Σ⁽ᵈ⁾ (X .s (xy .fst)) (sym (Y .s {xy .fst} (xy .snd)))]

{`
We can check this by hand too:

sst.Σ⁽ᵈ⁾ : (X : SST) (X' : SST⁽ᵈ⁾ X) (Y : SST⁽ᵈ⁾ X) (Y' : SST⁽ᵈᵈ⁾ X X' Y) : SST⁽ᵈ⁾ (sst.Σ X Y)
sst.Σ⁽ᵈ⁾ X (X .s (xy .fst)) Y : SST⁽ᵈᵈ⁾ X (X .s (xy .fst)) Y → SST⁽ᵈ⁾ (sst.Σ X Y)
X : SST
xy .fst : X .z
X .s (xy .fst) : SST⁽ᵈ⁾ X
Y : SST⁽ᵈ⁾ X
xy .snd : Y .z (xy .fst)
− .s : (X : SST) → X .z → SST⁽ᵈ⁾ X
− .s⁽ᵈ⁾ : {X : SST} (X' : SST⁽ᵈ⁾ X) (x : X .z) (x' : X' .z x) → SST⁽ᵈᵈ⁾ X X' (X .s x)
Y .s⁽ᵈ⁾ (xy .fst) (xy .snd) : SST⁽ᵈᵈ⁾ X Y (X .s (xy .fst))

So the type of "Y .s⁽ᵈ⁾ (xy .fst) (xy .snd)" is indeed symmetrized from what "sst.Σ⁽ᵈ⁾ X (X .s (xy .fst)) Y" expects for its argument.  (Note that ".s⁽ᵈ⁾" is not Narya syntax; the field projection has the same syntax at every dimension, I just wrote this for clarity in the by-hand version.)
`}

{` Constant displayed SSTs also require symmetry, as noted in the paper. `}
def sst.const (X Y : SST) : SST⁽ᵈ⁾ X ≔ [
| .z ↦ sig _ ↦ (
    ungel : Y .z )
| .s ↦ {x} y ↦ sym (sst.const⁽ᵈ⁾ (X .s x) (Y .s (y .ungel)))]

{` Using constant displayed SSTs, we can define binary sum SSTs. `}
def sst.sum (X Y : SST) : SST ≔ [
| .z ↦ data [
  | inl. (_ : X .z)
  | inr. (_ : Y .z) ]
| .s ↦ [
  | inl. x ↦ sst.sum⁽ᵈ⁾ (X .s x) (sst.const Y sst.∅)
  | inr. y ↦ sst.sum⁽ᵈ⁾ (sst.const X sst.∅) (Y .s y)]]

{` The product of a family of SSTs indexed by a discrete type. `}
def sst.discprod (A :△| Disc) (X : (a :△| A) → SST) : SST ≔ [
| .z ↦ (a :△| A) → X a .z
| .s ↦ p ↦ sst.discprod⁽ᵈ⁾ A {X} (a ↦ X a .s (p a))]

{` Augmented SSTs are another displayed coinductive. `}
def ASST : Type ≔ codata [ X .z : Type | X .s : ASST⁽ᵈ⁾ X ]

{` Every global type can be regarded as a synthetic augmented SST, hence an analytic one. `}
def asst.Int (X :△□| Type) : ASST ≔ [ .z ↦ X | .s ↦ asst.Int⁽ᵈ⁾ X ]

{` Every ASST has a fiber over a point that is an SST.  (Combining this with asst.Int produces sst.Fib). `}
def asst.Fib (X : ASST) (x : X .z) : SST ≔ [
| .z ↦ X .s .z x
| .s ↦ y ↦ asst.Fib⁽ᵈ⁾ (X .s) y]

{` Pointedness of an SST is another displayed coinductive. `}
def sst.pt (X : SST) : Type ≔ codata [
| p .z : X .z
| p .s : sst.pt⁽ᵈ⁾ (X .s (p .z)) p ]

{` As are maps of SSTs. `}
def sst.hom (X Y : SST) : Type ≔ codata [
| f .z : X .z → Y .z
| f .s : (x : X .z) → sst.hom⁽ᵈ⁾ (X .s x) (Y .s (f .z x)) f ]

{` Identities and composition for maps `}
def sst.id (X : SST) : sst.hom X X ≔ [
| .z ↦ x ↦ x
| .s ↦ x ↦ sst.id⁽ᵈ⁾ (X .s x)]

def sst.comp (X Y Z : SST) (g : sst.hom Y Z) (f : sst.hom X Y)
  : sst.hom X Z
  ≔ [
| .z ↦ x ↦ g .z (f .z x)
| .s ↦ x ↦
    sst.comp⁽ᵈ⁾ (X .s x) (Y .s (f .z x)) (Z .s (g .z (f .z x)))
      (g .s (f .z x)) (f .s x)]

{` Universal maps `}
def sst.abort (X : SST) : sst.hom sst.∅ X ≔ [ .z ↦ [ ] | .s ↦ [ ] ]

def sst.uniq (X : SST) : sst.hom X sst.𝟙 ≔ [
| .z ↦ _ ↦ ()
| .s ↦ x ↦ sst.uniq⁽ᵈ⁾ (X .s x)]

def sst.pair (X Y Z : SST) (f : sst.hom X Y) (g : sst.hom X Z)
  : sst.hom X (sst.prod Y Z)
  ≔ [
| .z ↦ x ↦ (f .z x, g .z x)
| .s ↦ x ↦
    sst.pair⁽ᵈ⁾ (X .s x) (Y .s (f .z x)) (Z .s (g .z x)) (f .s x) (g .s x)]

{` Copairing requires a displayed version of abort.  And for that, we can't match directly against (x' .ungel) since it isn't a variable, so we have to define a helper function first. `}
def sst.abortz (X : Type) : sst.∅ .z → X ≔ [ ]

def sst.const_abort (X Y : SST) (Y' : SST⁽ᵈ⁾ Y) (f : sst.hom X Y)
  : sst.hom⁽ᵈ⁾ (sst.const X sst.∅) Y' f
  ≔ [
| .z ↦ {x} x' ↦ sst.abortz (Y' .z (f .z x)) (x' .ungel)
| .s ↦ {x} x' ↦
    sst.abortz
      {` Ideally, this big long argument should be obtainable by unification. `}
      (sst.hom⁽ᵈᵈ⁾ {X} {sst.const X sst.∅} {X .s x}
         (sym (sst.const⁽ᵈ⁾ (X .s x) (sst.∅ .s (x' .ungel)))) {Y} {Y'}
         {Y .s (f .z x)}
         (Y' .s {f .z x} (sst.abortz (Y' .z (f .z x)) (x' .ungel))) {f}
         (sst.const_abort X Y Y' f) (f .s x)) (x' .ungel)]

def sst.copair (X Y Z : SST) (f : sst.hom X Z) (g : sst.hom Y Z)
  : sst.hom (sst.sum X Y) Z
  ≔ [
| .z ↦ [ inl. x ↦ f .z x | inr. y ↦ g .z y ]
| .s ↦ [
  | inl. x ↦
      sst.copair⁽ᵈ⁾ (X .s x) (sst.const Y sst.∅) (Z .s (f .z x)) (f .s x)
        (sst.const_abort Y Z (Z .s (f .z x)) g)
  | inr. y ↦
      sst.copair⁽ᵈ⁾ (sst.const X sst.∅) (Y .s y) (Z .s (g .z y))
        (sst.const_abort X Z (Z .s (g .z y)) f) (g .s y)]]
