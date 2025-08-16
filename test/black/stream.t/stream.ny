def Stream : Type → Type ≔ A ↦ codata [ _ .head : A | _ .tail : Stream A ]
axiom A : Type

{` We suppose a stream and take some parts of it`}
axiom s : Stream A
def s0 : A ≔ s .head
def s0t : Stream A ≔ s .tail
def s1 : A ≔ s .tail .head
def s2 : A ≔ s .tail .tail .head

{`With a non-corecursive copattern-match, we can define a one-step eta-expansion, and see that streams don't satisfy eta-conversion.`}
def s' : Stream A ≔ [ .head ↦ s .head | .tail ↦ s .tail ]
`def s_eq_s' : Id (Stream A) s s' := refl s

{`Their identity/bridge types are bisimulations.  We can use this to prove propositional one-step eta-conversion.`}
def s_is_s' : Id (Stream A) s s' ≔ [
| .head ↦ refl (s .head)
| .tail ↦ refl (s .tail)]

{`We can also define the general corecursor 'corec' by copattern-matching.`}
def corec : (A X : Type) → (X → A) → (X → X) → X → Stream A ≔ A X h t x ↦ [
| .head ↦ h x
| .tail ↦ corec A X h t (t x)]

{`Using corec, we can also define an infinitary eta-expansion.`}
def s'' : Stream A ≔ corec A (Stream A) (x ↦ x .head) (x ↦ x .tail) s
`def s_eq_s'' : Id (Stream A) s s'' := refl s

{`We can't prove (Id (Stream A) s s'') with a non-corecursive copattern-match (since it's more than one step) or with "refl corec" (since it can only equate two values of corec).  We need a more general bisimulation, which must be defined by a full coinduction, which in turn requires a new operation defined by a higher-dimensional copattern case tree.`}
def ∞eta : Stream A → Stream A ≔ s ↦ [
| .head ↦ s .head
| .tail ↦ ∞eta (s .tail)]
`def ∞eta_bisim' : Id (Stream A → Stream A) (s ↦ s) (s ↦ ∞eta s) ≔ refl (s ↦ ∞eta s)
def ∞eta_bisim : (s : Stream A) → Id (Stream A) s (∞eta s) ≔ s ↦ [
| .head ↦ refl (s .head)
| .tail ↦ ∞eta_bisim (s .tail)]

{`We construct a stream of natural numbers and check its first few elements`}
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
def nats : Stream ℕ ≔ corec ℕ ℕ (x ↦ x) (x ↦ suc. x) 0
def nats0_eq_0 : Id ℕ (nats .head) 0 ≔ refl (0 : ℕ)
def nats1_eq_1 : Id ℕ (nats .tail .head) 1 ≔ refl (1 : ℕ)
def nats2_eq_2 : Id ℕ (nats .tail .tail .head) 2 ≔ refl (2 : ℕ)
def nats3_eq_3 : Id ℕ (nats .tail .tail .tail .head) 3 ≔ refl (3 : ℕ)

{`Now we construct the stream of fibonacci numbers and check the first few of its elements`}
def plus : ℕ → ℕ → ℕ ≔ m n ↦ match n [ zero. ↦ m | suc. n ↦ suc. (plus m n) ]
def prod : Type → Type → Type ≔ A B ↦ sig ( fst : A, snd : B )
def fib : Stream ℕ
  ≔ corec ℕ (prod ℕ ℕ) (x ↦ x .fst)
      (x ↦ (fst ≔ x .snd, snd ≔ plus (x .fst) (x .snd))) (fst ≔ 1, snd ≔ 1)
def fib0_eq_1 : Id ℕ (fib .head) 1 ≔ refl (1 : ℕ)
def fib1_eq_1 : Id ℕ (fib .tail .head) 1 ≔ refl (1 : ℕ)
def fib2_eq_2 : Id ℕ (fib .tail .tail .head) 2 ≔ refl (2 : ℕ)
def fib3_eq_3 : Id ℕ (fib .tail .tail .tail .head) 3 ≔ refl (3 : ℕ)
def fib4_eq_5 : Id ℕ (fib .tail .tail .tail .tail .head) 5 ≔ refl (5 : ℕ)
def fib5_eq_8 : Id ℕ (fib .tail .tail .tail .tail .tail .head) 8
  ≔ refl (8 : ℕ)
