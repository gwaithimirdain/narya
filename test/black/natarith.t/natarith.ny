def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
def O : ℕ ≔ zero.
def S : ℕ → ℕ ≔ n ↦ suc. n
def plus : ℕ → ℕ → ℕ ≔ m n ↦ match n [ zero. ↦ m | suc. n ↦ suc. (plus m n) ]
def times : ℕ → ℕ → ℕ ≔ m n ↦ match n [
| zero. ↦ zero.
| suc. n ↦ plus (times m n) m]
def ℕ_ind
  : (P : ℕ → Type) (z : P zero.) (s : (n : ℕ) → P n → P (suc. n)) (n : ℕ)
    → P n
  ≔ P z s n ↦ match n [ zero. ↦ z | suc. n ↦ s n (ℕ_ind P z s n) ]

def zero : ℕ ≔ zero.
def one : ℕ ≔ suc. zero.
def two : ℕ ≔ suc. (suc. zero.)
def three : ℕ ≔ suc. (suc. (suc. zero.))
def four : ℕ ≔ suc. (suc. (suc. (suc. zero.)))

{`Identity types `}
def id00 : Id ℕ zero. zero. ≔ zero.
def id00' : Id ℕ zero. zero. ≔ refl (zero. : ℕ)
def id00'' : Id ℕ zero zero ≔ refl zero
def id11 : Id ℕ one one ≔ refl one

def congsuc : (x : ℕ) (y : ℕ) → Id ℕ x y → Id ℕ (suc. x) (suc. y)
  ≔ x y p ↦ suc. p

def cong2suc
  : (x00 : ℕ) (x01 : ℕ) (x02 : Id ℕ x00 x01) (x10 : ℕ) (x11 : ℕ)
    (x12 : Id ℕ x10 x11) (x20 : Id ℕ x00 x10) (x21 : Id ℕ x01 x11)
    (x22 : Id (Id ℕ) x02 x12 x20 x21)
    → (Id (Id ℕ) {suc. x00} {suc. x01} (suc. x02) {suc. x10} {suc. x11}
         (suc. x12) (suc. x20) (suc. x21))
  ≔ x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦ suc. x22

{`Addition`}
def one_plus_one_eq_two : Id ℕ (plus one one) two ≔ refl two
def one_plus_two_eq_three : Id ℕ (plus one two) three ≔ refl three
def two_plus_zero_eq_two : Id ℕ (plus two zero) two ≔ refl two
def zero_plus_zero_eq_zero : Id ℕ (plus zero zero) zero ≔ refl zero
def zero_plus_one_eq_one : Id ℕ (plus zero one) one ≔ refl one
def zero_plus_two_eq_two : Id ℕ (plus zero two) two ≔ refl two

{`Refl of a constant still computes`}
def r000 : Id (Id ℕ zero zero) (refl (plus zero zero)) (refl zero)
  ≔ refl (refl zero)

def r112 : Id (Id ℕ two two) (refl (plus one one)) (refl two)
  ≔ refl (refl two)

{`We can also define addition with the general recursor/inductor`}
def rplus : ℕ → ℕ → ℕ ≔ m n ↦ ℕ_ind (_ ↦ ℕ) m (_ IH ↦ suc. IH) n

def one_plus_one_eq_two' : Id ℕ (rplus one one) two ≔ refl two
def one_plus_two_eq_three' : Id ℕ (rplus one two) three ≔ refl three
def two_plus_zero_eq_two' : Id ℕ (rplus two zero) two ≔ refl two
def zero_plus_zero_eq_zero' : Id ℕ (rplus zero zero) zero ≔ refl zero
def zero_plus_one_eq_one' : Id ℕ (rplus zero one) one ≔ refl one
def zero_plus_two_eq_two' : Id ℕ (rplus zero two) two ≔ refl two

{`And prove by induction that it equals the other one.  Note that this uses ap on suc.`}
def plus_is_rplus : (x : ℕ) (y : ℕ) → Id ℕ (plus x y) (rplus x y)
  ≔ x y ↦ ℕ_ind (u ↦ Id ℕ (plus x u) (rplus x u)) (refl x) (u q ↦ suc. q) y

{`We also have multiplication`}

def one_times_zero_eq_zero : Id ℕ (times one zero) zero ≔ refl zero
def zero_times_one_eq_zero : Id ℕ (times zero one) zero ≔ refl zero
def one_times_one_eq_one : Id ℕ (times one one) one ≔ refl one
def two_times_two_eq_four : Id ℕ (times two two) four ≔ refl four
