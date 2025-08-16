{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-arity" "0" "-direction" "w,wk") -*- `}

def И (A : Type) : Type ≔ codata [ x .subst.w : A.0 . ]

def toИ (A : Type) (a : A) : И A ≔ [ .subst.w ↦ a.0 ]

axiom A : Type

axiom a : wk (И A) .

echo a .subst

axiom b : wk (wk (И A)) . .

echo b .subst.1

echo b .subst.2
