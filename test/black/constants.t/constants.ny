{`Church numerals`}
def CN : Type ≔ (A : Type) → (A → A) → (A → A)
def zero : CN ≔ A f x ↦ x
def one : CN ≔ A f x ↦ f x
def two : CN ≔ A f x ↦ f (f x)
def three : CN ≔ A f x ↦ f (f (f x))
def four : CN ≔ A f x ↦ f (f (f (f x)))
def one_eq : Id CN one one ≔ refl one
def cplus : CN → CN → CN ≔ m n A f x ↦ m A f (n A f x)
def cplus_one_one_eq_two : Id CN (cplus one one) (two) ≔ refl two
def ctimes : CN → CN → CN ≔ m n A f x ↦ m A (n A f) x
def ctimes_two_two_eq_four : Id CN (ctimes two two) (four) ≔ refl four

{`Sigma-types`}
def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def zero_zero : Σ CN (_ ↦ CN) ≔ (zero, zero)
def zero_zero_fst_eq_zero : Id CN (zero_zero .fst) zero ≔ refl zero
def zero_zero_snd_eq_zero : Id CN (zero_zero .snd) zero ≔ refl zero
axiom A : Type
axiom B : A → Type
axiom a : A
axiom b : B a
def ab : Σ A B ≔ (fst ≔ a, snd ≔ b)
def ab_fst_eq_a : Id A (ab .fst) a ≔ refl a
def ab_snd_eq_b : Id (B a) (ab .snd) b ≔ refl b
def ab_fst_eq_a' : Id A (ab .0) a ≔ refl a
def ab_snd_eq_b' : Id (B a) (ab .1) b ≔ refl b
def zero_zero' : Σ CN (_ ↦ CN) ≔ (fst ≔ zero, snd ≔ zero)
def zero_zero_eq_zero_zero' : Id (Σ CN (_ ↦ CN)) zero_zero zero_zero'
  ≔ refl zero_zero

{` Pi-types `}
{`These are built in, of course, but we also have a named constant for them.`}

def built_in_pi_eqs_named_pi : Id Type ((x : A) → B x) (Π A B) ≔ refl (Π A B)

{`In particular, this gives a way for the user to write higher-dimensional Π-types.`}
def refl_for_pi
  : Id (Id Type ((x : A) → B x) ((x : A) → B x)) (refl ((x : A) → B x))
      (refl Π (refl A) (refl B))
  ≔ refl (refl ((x : A) → B x))

{`Coinductive streams`}
def Stream : Type → Type ≔ A ↦ codata [ _ .head : A | _ .tail : Stream A ]
def zeros : Stream CN ≔ [ .head ↦ zero | .tail ↦ zeros ]
def zeros_first_term_eq_zero : Id CN (zeros .head) (zero) ≔ refl zero
def zeros_second_term_eq_zero : Id CN (zeros .tail .head) (zero) ≔ refl zero
def zeros_third_term_eq_zero : Id CN (zeros .tail .tail .head) (zero)
  ≔ refl zero
def zeros_fourth_term_eq_zero : Id CN (zeros .tail .tail .tail .head) (zero)
  ≔ refl zero

def nats : CN → Stream CN ≔ n ↦ [ .head ↦ n | .tail ↦ nats (cplus n one) ]
def nats_zero_third_term_eq_two : Id CN (nats zero .tail .tail .head) two
  ≔ refl two
def nats_zero_fifth_term_eq_four
  : Id CN (nats zero .tail .tail .tail .tail .head) four
  ≔ refl four

{`Bisimulation`}
def ∞eta : Stream A → Stream A ≔ s ↦ [
| .head ↦ s .head
| .tail ↦ ∞eta (s .tail)]
def ∞eta_bisim : (s : Stream A) → Id (Stream A) s (∞eta s) ≔ s ↦ [
| .head ↦ refl (s .head)
| .tail ↦ ∞eta_bisim (s .tail)]

{`Natural numbers`}
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
def Nat : Type ≔ ℕ
def plus : ℕ → ℕ → ℕ ≔ m n ↦ match n [ zero. ↦ m | suc. n ↦ suc. (plus m n) ]
def times : ℕ → ℕ → ℕ ≔ m n ↦ match n [
| zero. ↦ zero.
| suc. n ↦ plus (times m n) m]

{`Lists`}
def List : Type → Type ≔ A ↦ data [ nil. | cons. (x : A) (xs : List A) ]
def append : (A : Type) → List A → List A → List A ≔ A xs ys ↦ match xs [
| nil. ↦ ys
| cons. x xs ↦ cons. x (append A xs ys)]
def append_eq_sample
  : Id (List ℕ) (append ℕ (cons. 0 nil.) (cons. 1 (cons. 2 nil.)))
      (cons. 0 (cons. 1 (cons. 2 nil.)))
  ≔ refl (append ℕ (cons. 0 nil.) (cons. 1 (cons. 2 nil.)))

{`Vectors`}
def Vec : Type → ℕ → Type ≔ A ↦ data [
| nil. : Vec A 0
| cons. : (n : ℕ) → A → Vec A n → Vec A (suc. n) ]
def lplus : ℕ → ℕ → ℕ ≔ m n ↦ match m [
| zero. ↦ n
| suc. m ↦ suc. (lplus m n)]
def vappend : (A : Type) (m n : ℕ) → Vec A m → Vec A n → Vec A (lplus m n)
  ≔ A m n xs ys ↦ match xs [
| nil. ↦ ys
| cons. k z zs ↦ cons. (lplus k n) z (vappend A k n zs ys)]
def vappend_eq_sample
  : Id (Vec ℕ 3)
      (vappend ℕ 1 2 (cons. 0 0 nil.) (cons. 1 1 (cons. 0 2 nil.)))
      (cons. 2 0 (cons. 1 1 (cons. 0 2 nil.)))
  ≔ refl (vappend ℕ 1 2 (cons. 0 0 nil.) (cons. 1 1 (cons. 0 2 nil.)))

{`Matching lambda`}
def exp : ℕ → ℕ → ℕ ≔ m ↦ [ zero. ↦ suc. zero. | suc. n ↦ times (exp m n) m ]
def exp_eq_sample : Id ℕ (exp 3 2) 9 ≔ refl (9 : ℕ)
def exp2 : ℕ → ℕ → ℕ ≔ m ↦ [
| zero. ↦ suc. zero.
| suc. n ↦ times (exp m n) m]
def exp_eq_sample' : Id ℕ (exp2 2 3) 8 ≔ refl (8 : ℕ)

{`Empty Type`}
def ∅ : Type ≔ data []
def abort1 : (A : Type) → ∅ → A ≔ A ↦ [ ]
def abort2 : (A : Type) → ∅ → A ≔ A x ↦ match x [ ]

{`Higher-dimensional lambdas in case trees.  This simple version doesn't actually need them, as it could be just an ordinary higher-dimensional lambda term at a leaf.`}
axiom f : (x : A) → B x
def reflf : Id ((x : A) → B x) f f ≔ {x₀} {x₁} x₂ ↦ refl f x₂
def reflf_eq_reflf : Id (Id ((x : A) → B x) f f) reflf (refl f)
  ≔ refl (refl f)
{`To test that we actually allow higher-dimensional lambdas in case trees, we need to do some case-tree-only thing inside the lambda, like a match.`}
def refl_abort_f : ∅ → Id ((x : A) → B x) f f ≔ e {x₀} {x₁} x₂ ↦ match e [ ]
def refl_nat_f : ℕ → Id ((x : A) → B x) f f ≔ n {x₀} {x₁} x₂ ↦ match n [
| zero. ↦ refl f x₂
| suc. _ ↦ refl f x₂]
def refl_nat_f_eq_reflf
  : Id (Id ((x : A) → B x) f f) (refl_nat_f zero.) (refl f)
  ≔ refl (refl f)

{`We also test cube variable abstraction syntax `}
def refl_abort_f_cube : ∅ → Id ((x : A) → B x) f f ≔ e ↦ x ⤇ match e [ ]
def refl_nat_f_cube : ℕ → Id ((x : A) → B x) f f ≔ n ↦ x ⤇ match n [
| zero. ↦ refl f x.2
| suc. _ ↦ refl f x.2]
{`These are actually *unequal* because definition by case trees is generative. But they become equal when evaluated at concrete numbers so that the case trees compute away.`}
def evaluated_eq_sample
  : Id (Id ((x : A) → B x) f f) (refl_nat_f 3) (refl_nat_f_cube 3)
  ≔ refl (refl_nat_f 3)

{`Higher-dimensional matches`}
def foo : (x y : ℕ) → Id ℕ x y → ℕ ≔ x y p ↦ match p [
| zero. ⤇ 0
| suc. n ⤇ 1]
def bar : (x y : ℕ) → Id ℕ x y → ℕ ≔ x y ↦ [ zero. ⤇ zero. | suc. p ⤇ p.0 ]
def bar_eq_sample : Id ℕ (bar 1 1 (refl (1 : ℕ))) 0 ≔ refl (0 : ℕ)
def bar_eq_sample' : Id ℕ (bar 2 2 (refl (2 : ℕ))) 1 ≔ refl (1 : ℕ)
def prec : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ n ]
def idnat : (x y : ℕ) → Id ℕ x y → Id ℕ x y ≔ x y ↦ [
| zero. ⤇ zero.
| suc. p ⤇ suc. p.2]
def apprec : (x y : ℕ) → Id ℕ x y → Id ℕ (prec x) (prec y)
  ≔ x y p ↦ match p [ zero. ⤇ zero. | suc. p ⤇ p.2 ]
def ⊤ : Type ≔ sig ()
def code : ℕ → ℕ → Type ≔ [
| zero. ↦ [ zero. ↦ ⊤ | suc. _ ↦ ∅ ]
| suc. m ↦ [ zero. ↦ ∅ | suc. n ↦ code m n ]]
def rcode : (x : ℕ) → code x x ≔ [ zero. ↦ () | suc. n ↦ rcode n ]
def encode : (x y : ℕ) → Id ℕ x y → code x y ≔ x y ↦ [
| zero. ⤇ ()
| suc. p ⤇ encode p.0 p.1 p.2]
def decode : (x y : ℕ) → code x y → Id ℕ x y ≔ x y c ↦ match x [
| zero. ↦ match y [ zero. ↦ zero. | suc. _ ↦ match c [ ] ]
| suc. x ↦ match y [ zero. ↦ match c [ ] | suc. y ↦ suc. (decode x y c) ]]
def encode_decode
  : (x y : ℕ) (c : code x y) → Id (code x y) (encode x y (decode x y c)) c
  ≔ [
| zero. ↦ [ zero. ↦ _ ↦ () | suc. _ ↦ [ ] ]
| suc. x ↦ [ zero. ↦ [ ] | suc. y ↦ c ↦ encode_decode x y c ]]
def decode_encode
  : (x y : ℕ) (p : Id ℕ x y) → Id (Id ℕ x y) (decode x y (encode x y p)) p
  ≔ x y ↦ [ zero. ⤇ zero. | suc. p ⤇ suc. (decode_encode p.0 p.1 p.2) ]

{`Matching on a boundary of a cube variable.`}
def mtchbd0 : (e : ∅) (f : ℕ → ℕ) → Id (ℕ → ℕ) f f ≔ e f ↦ n ⤇ match n.0 [
| zero. ↦ match e [ ]
| suc. _ ↦ match e [ ]]

def mtchbd0' : (e : ∅) (f : ℕ → ℕ) → Id (ℕ → ℕ) f f ≔ e f ↦ n ⤇ match n.0 [
| zero. ↦ match e [ ]
| suc. _ ↦ refl f n.2]

def mtchbd0'' : (e : ∅) (f : ℕ → ℕ) → Id (ℕ → ℕ) f f
  ≔ e f {n0} {n1} n2 ↦ match n0 [ zero. ↦ match e [ ] | suc. _ ↦ refl f n2 ]

{`Matching inside a tuple `}
def mtchtup : ℕ → Σ Type (X ↦ (X → X)) ≔ n ↦ (
  match n [ zero. ↦ ℕ | suc. _ ↦ ℕ ],
  x ↦ x)
def mtchtup2 : ℕ → Σ ℕ (x ↦ Id ℕ x 0) ≔ n ↦ (
  fst ≔ match n [ zero. ↦ 0 | suc. _ ↦ 0 ],
  snd ≔ match n [ zero. ↦ refl (0 : Nat) | suc. _ ↦ refl (0 : Nat) ])

{`Covectors (canonical types defined inside a match)`}
def Covec : Type → ℕ → Type ≔ A n ↦ match n [
| zero. ↦ sig ()
| suc. n ↦ sig (
    car : A,
    cdr : Covec A n )]
def nil : Covec ℕ 0 ≔ ()
def onetwo : Covec ℕ 2 ≔ (1, (2, ()))
def covec_eq_sample : Id ℕ (onetwo .0) 1 ≔ refl (1 : ℕ)
def covec_eq_sample' : Id ℕ (onetwo .1 .0) 2 ≔ refl (2 : ℕ)
def covec_eq_sample'' : Id (Covec ℕ 0) (onetwo .1 .1) ()
  ≔ refl (onetwo .1 .1)
def coconcat
  : (A : Type) (m n : ℕ) → Covec A m → Covec A n → Covec A (lplus m n)
  ≔ A m n v w ↦ match m [
| zero. ↦ w
| suc. m ↦ (v .0, coconcat A m n (v .1) w)]
