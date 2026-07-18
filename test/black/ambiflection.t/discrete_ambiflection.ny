{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-arity" "1" "-discrete-ambiflection") -*- `}

` △□ is a *discrete* self-adjoint (co)monad on Type: working under a △□ lock filters out the
` parametric dimension, exactly like -discrete-ambiflector's ♮ (of which △□ here is the two-mode
` analogue) and -discrete-tconn's △◇ (both of which also have a reflector unit into a discrete
` modality, hence also require arity 1).

axiom X : Type

axiom A : Type

axiom B : Type

axiom f : (x : X) (y :△□| A) → B

axiom a : (x : X) → A

axiom x₀ : X

axiom x₁ : Br X x₀

synth rel (x ↦ f x (a x)) x₁

echo rel (x ↦ f x (a x)) x₁
