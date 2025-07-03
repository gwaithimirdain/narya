{` -*- narya-prog-args: ("-proofgeneral" "-arity" "0" "-direction" "w,wk") -*- `}

axiom A : Type
echo wk A
echo A⁽ʷ⁾
echo wk (wk A)

axiom a : A
echo wk a
echo wk (wk a)

axiom a' : wk A .
echo a'
echo wk a'
echo sym (wk a')

axiom a'' : A⁽ʷʷ⁾ . .
echo a''
echo sym a''
echo wk a''
echo sym (wk a'')

axiom B : Type⁽ʷ⁾ .
axiom b : B .
echo b
echo wk b
echo sym (wk b)

axiom C : Type⁽ʷʷ⁾ . .
axiom c : C . .
echo c
echo sym c
echo wk c
echo sym (wk c)
echo wk (sym c)
