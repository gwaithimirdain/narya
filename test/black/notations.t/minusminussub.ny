import "minus"

notation 0 minus : "-" x ≔ ℤ.minus x
notation 0 minus' : "-" x ≔ ℤ.minus x

notation 0 sub : x "-" y ≔ ℤ.sub x y

echo three - one
echo one - three
echo two - zero
echo zero - two
echo - two
