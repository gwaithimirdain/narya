{` -*- narya-prog-args: ("-proofgeneral" "-discreteness" "-dtt") -*- `}

{` We can define higher display of a modal type at arbitrary dimensions, mutually recursively along with its boundary. `}

def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

{` This shouldn't be necessary if we could use ℕ:Disc behind a △ window, but I haven't figured out how to deal with nonparametric window modalities yet. `}
def ℕᵈ (n : ℕ) : ℕ⁽ᵈ⁾ n ≔ match n [ zero. ↦ zero. | suc. n ↦ suc. (ℕᵈ n) ]

def ∂ (n : ℕ) (A :△□| Type) : Type ≔ match n [
| zero. ↦ sig ()
| suc. n ↦ sig (
    ∂x : ∂ n A,
    x : d n A ∂x,
    ∂x′ : ∂⁽ᵈ⁾ (ℕᵈ n) A ∂x )]

and d (n : ℕ) (A :△□| Type) (∂x : ∂ n A) : Type ≔ match n [
| zero. ↦ A
| suc. n ↦ d⁽ᵈ⁾ (ℕᵈ n) A {∂x .∂x} (∂x .∂x′) (∂x .x)]

axiom A : Type

def ∂0 : ∂ 0 A ≔ ()
def d0 (a : A) : d 0 A ∂0 ≔ a

def ∂1 (a : A) : ∂ 1 A ≔ (∂0, a, ())
def d1 (a : A) (a′ : A⁽ᵈ⁾ a) : d 1 A (∂1 a) ≔ a′

def ∂2 (a : A) (a′ : A⁽ᵈ⁾ a) (a″ : A⁽ᵈ⁾ a) : ∂ 2 A ≔ (
  ∂1 a,
  a″,
  ((), a′, ()))
def d2 (a : A) (a′ : A⁽ᵈ⁾ a) (a″ : A⁽ᵈ⁾ a) (a‴ : A⁽ᵈᵈ⁾ a′ a″)
  : d 2 A (∂2 a a′ a″)
  ≔ a‴

