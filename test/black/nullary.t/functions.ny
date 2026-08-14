option parametric ≔ arity 0, letter w, name wk

axiom A : Type
axiom B : A → Type

echo wk ((x : A) → B x)
echo wk ((x : A) → B x) .
echo wk (wk ((x : A) → B x))
echo wk (wk ((x : A) → B x)) .
echo wk (wk ((x : A) → B x)) . .

axiom f : (x : A) → B x
echo wk f
echo wk (wk f)
