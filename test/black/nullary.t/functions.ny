{` -*- narya-prog-args: ("-proofgeneral" "-arity" "0" "-direction" "w,wk") -*- `}

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
