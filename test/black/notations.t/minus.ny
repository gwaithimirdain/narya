def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def ℕ.plus (a b : ℕ) : ℕ ≔ match b [ zero. ↦ a | suc. b ↦ suc. (ℕ.plus a b) ]

def ℤ : Type ≔ data [ zero. | suc. (_ : ℕ) | negsuc. (_ : ℕ) ]

def zero : ℤ ≔ zero.
def one : ℤ ≔ suc. zero.
def two : ℤ ≔ suc. (suc. zero.)
def three : ℤ ≔ suc. (suc. (suc. zero.))
def minus_one : ℤ ≔ negsuc. zero.
def minus_two : ℤ ≔ negsuc. (suc. zero.)
def minus_three : ℤ ≔ negsuc. (suc. (suc. zero.))

def ℤ.minus : ℤ → ℤ ≔ [
| zero. ↦ zero.
| suc. n ↦ negsuc. n
| negsuc. n ↦ suc. n]

def ℕ.sub (a b : ℕ) : ℤ ≔ match a, b [
| zero., zero. ↦ zero.
| suc. a, zero. ↦ suc. a
| zero., suc. b ↦ negsuc. b
| suc. a, suc. b ↦ ℕ.sub a b]

def ℤ.sub (a b : ℤ) : ℤ ≔ match b [
| zero. ↦ a
| suc. b ↦ match a [
  | zero. ↦ negsuc. b
  | suc. a ↦ ℕ.sub a b
  | negsuc. a ↦ negsuc. (suc. (ℕ.plus a b))]
| negsuc. b ↦ match a [
  | zero. ↦ suc. b
  | suc. a ↦ suc. (suc. (ℕ.plus a b))
  | negsuc. a ↦ ℕ.sub b a]]

echo ℤ.sub three one
echo ℤ.sub one three
echo ℤ.sub two zero
echo ℤ.sub zero two
echo ℤ.sub minus_three minus_one
echo ℤ.sub minus_one minus_three
echo ℤ.sub minus_two zero
echo ℤ.sub zero minus_two
echo ℤ.sub two minus_two
echo ℤ.sub minus_two two
echo ℤ.sub two two
echo ℤ.sub minus_two minus_two
