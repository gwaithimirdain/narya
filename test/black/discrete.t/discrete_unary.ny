{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-arity" "1" "-discrete-tconn") -*- `}

axiom X : Type
axiom A : Type
axiom B : Type
axiom f : (x : X) (y :△◇| A) → B
axiom a : (x : X) → A
axiom x₀ : X
axiom x₁ : Br X x₀

synth rel (x ↦ f x (a x)) x₁
echo rel (x ↦ f x (a x)) x₁
