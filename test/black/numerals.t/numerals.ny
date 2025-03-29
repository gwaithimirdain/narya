def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
def ℕ₊ : Type ≔ data [ one. | suc. (_ : ℕ₊) ]
def ℚ₀₊ : Type ≔ data [ zero. | suc. (_ : ℕ) | quot. (_ : ℕ) (_ : ℕ₊) ]

section ℕ ≔
  def zero : ℕ ≔ 0
  def one : ℕ ≔ 1
  echo one
  def one' : ℕ ≔ 1.0
  echo one'
  def two : ℕ ≔ 2
end

section ℚ ≔
  def zero : ℚ₀₊ ≔ 0
  def one : ℚ₀₊ ≔ 1
  def two : ℚ₀₊ ≔ 2.0
  echo two
  def half : ℚ₀₊ ≔ 0.5
  echo half
  def quart : ℚ₀₊ ≔ 0.25
  echo quart
end
