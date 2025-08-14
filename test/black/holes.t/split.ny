{` This file is NOT executed by run.t.  It's for manual testing of the PG split function C-c C-y. `}

def ℕ : Type ≔ data [ zero. | suc. (n : ℕ) ]

def plus (m n : ℕ) : ℕ ≔ match m, n [
| zero., zero. ↦ ¿ʔ
| zero., suc. n ↦ ¿ʔ
| suc. m, zero. ↦ ¿ʔ
| suc. m, suc. n ↦ ¿ʔ]

def ⊥ : Type ≔ data []

def foo (x : ℕ) (y : ⊥) : Type ≔ ¿ʔ

def bar (x : ℕ) (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : Type ≔ ¿ʔ

def baz : Type ≔ data [ baz. (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) ]

def bazzz (x : baz) : Type ≔ match x [
| baz. _ _ zero. ⤇ ℕ
| baz. _ _ (suc. n) ⤇ bazzz (baz. n.0 n.1 n.2)]

def f : (a : ℕ) (b : ℕ) → Type ≔ ¿ʔ

axiom g : ℕ → ℕ
def ge : Id ((x : ℕ) → ℕ) g g ≔ ¿ʔ

def ℕ×ℕ : Type ≔ sig ( fst : ℕ, snd : ℕ )

def nn : ℕ×ℕ ≔ ¿ʔ

axiom mm : ℕ×ℕ
def mme : Id ℕ×ℕ mm mm ≔ ¿ʔ

def Sℕ : Type ≔ codata [ s .head : ℕ | s .tail : Sℕ ]

def sn : Sℕ ≔ ¿ʔ
axiom sm : Sℕ
def sme : Id Sℕ sm sm ≔ ¿ʔ

def √ℕ : Type ≔ codata [ x .root.e : ℕ ]

def qn : √ℕ ≔ ¿ʔ
axiom qm : √ℕ
def qme : Id √ℕ qm qm ≔ ¿ʔ
