import "minus"

notation(0) x "-" y ≔ ℤ.sub x y

notation(0) "-" x ≔ ℤ.minus x

echo three - one
echo one - three
echo two - zero
echo zero - two
echo - two
echo - minus_two
echo - zero
echo zero - zero

notation(0) "-" x ≔ ℤ.minus x

echo three - one
echo - two
