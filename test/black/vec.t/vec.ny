def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
def Vec : Type → ℕ → Type ≔ A ↦ data [
| nil. : Vec A 0
| cons. : (n : ℕ) → A → Vec A n → Vec A (suc. n) ]

def ℕ_ind
  : (P : ℕ → Type) (z : P zero.) (s : (n : ℕ) → P n → P (suc. n)) (n : ℕ)
    → P n
  ≔ P z s n ↦ match n [ zero. ↦ z | suc. n ↦ s n (ℕ_ind P z s n) ]

def Vec_ind
  : (A : Type) (P : (n : ℕ) → Vec A n → Type) (pn : P zero. nil.)
    (pc : (n : ℕ) (a : A) (v : Vec A n) → P n v → P (suc. n) (cons. n a v))
    (n : ℕ) (v : Vec A n)
    → P n v
  ≔ A P pn pc n v ↦ match v [
| nil. ↦ pn
| cons. n a v ↦ pc n a v (Vec_ind A P pn pc n v)]

axiom A : Type
axiom a : A

{`Identity types`}
def id00 : Id (Vec A 0) nil. nil. ≔ nil.
def id11 : Id (Vec A 1) (cons. 0 a nil.) (cons. 0 a nil.)
  ≔ cons. 0 (refl a) nil.
def id22
  : Id (Vec A 2) (cons. 1 a (cons. 0 a nil.)) (cons. 1 a (cons. 0 a nil.))
  ≔ cons. 1 (refl a) (cons. 0 (refl a) nil.)

{`Check that the induction principle has the right type`}
def indty
  ≔ (A : Type) (P : (n : ℕ) → Vec A n → Type) (pn : P zero. nil.)
    (pc : (n : ℕ) (a : A) (v : Vec A n) → P n v → P (suc. n) (cons. n a v))
    (n : ℕ) (v : Vec A n)
    → P n v

def indty'
  ≔ (A : Type) (C : (n : ℕ) (xs : Vec A n) → Type) → C 0 nil. →
    ((n : ℕ) (x : A) (xs : Vec A n) → C n xs → C (suc. n) (cons. n x xs)) →
    (n : ℕ) (xs : Vec A n)
    → C n xs

def indty_eq_indty' : Id Type indty indty' ≔ refl indty

{`We can define concatenation by induction.  But it works better with a left-recursive version of nat addition.`}
def lplus : ℕ → ℕ → ℕ ≔ m n ↦ ℕ_ind (_ ↦ ℕ) n (_ IH ↦ suc. IH) m
{`And we prove that addition is associative`}
def lplusassoc
  : (m n k : ℕ) → Id ℕ (lplus (lplus m n) k) (lplus m (lplus n k))
  ≔ m n k ↦
    ℕ_ind (m ↦ Id ℕ (lplus (lplus m n) k) (lplus m (lplus n k)))
      (refl (lplus n k)) (_ IH ↦ suc. IH) m
{`And right unital`}
def lplusru : (m : ℕ) → Id ℕ (lplus m 0) m
  ≔ m ↦ ℕ_ind (m ↦ Id ℕ (lplus m 0) m) (refl (0 : ℕ)) (_ IH ↦ suc. IH) m

{`Now we can define concatenation`}
def concat : (A : Type) (m n : ℕ) → Vec A m → Vec A n → Vec A (lplus m n)
  ≔ A m n xs ys ↦
    Vec_ind A (m _ ↦ Vec A (lplus m n)) ys
      (m x xs IH ↦ cons. (lplus m n) x IH) m xs

axiom a0 : A
axiom a1 : A
axiom a2 : A
axiom a3 : A
axiom a4 : A
def ra01 : Vec A 2 ≔ cons. 1 a0 (cons. 0 a1 nil.)
def ra234 : Vec A 3 ≔ cons. 2 a2 (cons. 1 a3 (cons. 0 a4 nil.))
def a01_234 : Vec A 5 ≔ concat A 2 3 ra01 ra234
def a01234 : Vec A 5
  ≔ cons. 4 a0 (cons. 3 a1 (cons. 2 a2 (cons. 1 a3 (cons. 0 a4 nil.))))
def a01_234_eq_a01234 : Id (Vec A 5) a01_234 a01234 ≔ refl a01234

{`We can prove that concatenation is associative, "over" associativity of addition.`}
def concatassoc
  : (A : Type) (m n k : ℕ) (xs : Vec A m) (ys : Vec A n) (zs : Vec A k)
    → Id (Vec A) (lplus (lplus m n) k) (lplus m (lplus n k))
        (lplusassoc m n k) (concat A (lplus m n) k (concat A m n xs ys) zs)
        (concat A m (lplus n k) xs (concat A n k ys zs))
  ≔ A m n k xs ys zs ↦
    Vec_ind A
      (m xs ↦
       Id (Vec A) (lplus (lplus m n) k) (lplus m (lplus n k))
         (lplusassoc m n k) (concat A (lplus m n) k (concat A m n xs ys) zs)
         (concat A m (lplus n k) xs (concat A n k ys zs)))
      (refl (concat A n k ys zs))
      (m x xs IH ↦ cons. (lplusassoc m n k) (refl x) IH) m xs

{`And similarly right unital.`}
def concatru
  : (A : Type) (m : ℕ) (xs : Vec A m)
    → Id (Vec A) (lplus m 0) m (lplusru m) (concat A m 0 xs nil.) xs
  ≔ A m xs ↦
    Vec_ind A
      (m xs ↦ Id (Vec A) (lplus m 0) m (lplusru m) (concat A m 0 xs nil.) xs)
      nil. (m x xs IH ↦ cons. (lplusru m) (refl x) IH) m xs
