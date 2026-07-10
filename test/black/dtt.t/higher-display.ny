{` -*- narya-prog-args: ("-proofgeneral" "-discreteness" "-dtt") -*- `}

{` We can define higher display of a modal type at arbitrary dimensions, mutually recursively along with its boundary. `}

def ℕ : Disc ≔ data [ zero. | suc. (_ : ℕ) ]

def ∂ (n :△| ℕ) (A :△□| Type) : Type ≔ match (n :△| _) [
| zero. ↦ sig ()
| suc. n ↦ sig (
    ∂x : ∂ n A,
    x : d n A ∂x,
    ∂x′ : ∂⁽ᵈ⁾ n A ∂x )]

and d (n :△| ℕ) (A :△□| Type) (∂x : ∂ n A) : Type ≔ match (n :△| _) [
| zero. ↦ A
| suc. n ↦ d⁽ᵈ⁾ n A {∂x .∂x} (∂x .∂x′) (∂x .x)]

axiom A : Type

def ∂0 : ∂ 0 A ≔ ()
def d0 (a : A) : d 0 A ∂0 ≔ a

def ∂1 (a : A) : ∂ 1 A ≔ (∂0, a, ∂0⁽ᵈ⁾)
def d1 (a0 : A) (a1 : A⁽ᵈ⁾ a0) : d 1 A (∂1 a0) ≔ a1

def ∂2 (a00 : A) (a01 : A⁽ᵈ⁾ a00) (a10 : A⁽ᵈ⁾ a00) : ∂ 2 A ≔ (
  ∂1 a00,
  a01,
  ∂1⁽ᵈ⁾ a10)
def d2 (a00 : A) (a01 : A⁽ᵈ⁾ a00) (a10 : A⁽ᵈ⁾ a00) (a11 : A⁽ᵈᵈ⁾ a01 a10)
  : d 2 A (∂2 a00 a01 a10)
  ≔ sym a11

def ∂3 (a000 : A) (a001 a010 : A⁽ᵈ⁾ a000) (a011 : A⁽ᵈᵈ⁾ a001 a010)
  (a100 : A⁽ᵈ⁾ a000) (a101 : A⁽ᵈᵈ⁾ a001 a100) (a110 : A⁽ᵈᵈ⁾ a010 a100)
  : ∂ 3 A
  ≔ (
  ∂x ≔ ∂2 a000 a001 a010,
  x ≔ sym a011,
  ∂x′ ≔ ∂2⁽ᵈ⁾ a100 (sym a101) (sym a110))
def d3 (a000 : A) (a001 a010 : A⁽ᵈ⁾ a000) (a011 : A⁽ᵈᵈ⁾ a001 a010)
  (a100 : A⁽ᵈ⁾ a000) (a101 : A⁽ᵈᵈ⁾ a001 a100) (a110 : A⁽ᵈᵈ⁾ a010 a100)
  (a111 : A⁽ᵈᵈᵈ⁾ a011 a101 a110)
  : d 3 A (∂3 a000 a001 a010 a011 a100 a101 a110)
  ≔ a111⁽³²¹⁾
