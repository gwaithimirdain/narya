{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-arity" "1" "-discrete-ambiflector") -*- `}

` ♮ is a *discrete* self-adjoint (co)monad: working under a ♮ lock filters out the parametric
` dimension, exactly like -discrete-tconn's △◇ (which also has a reflector unit 1 ⇒ △◇, hence
` also requires arity 1).

axiom X : Type
axiom A : Type
axiom B : Type
axiom f : (x : X) (y :♮| A) → B
axiom a : (x : X) → A
axiom x₀ : X
axiom x₁ : Br X x₀

synth rel (x ↦ f x (a x)) x₁
echo rel (x ↦ f x (a x)) x₁
