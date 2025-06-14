{` Degeneracy notations `}

{` Simple refl `}

axiom A : Type

axiom a : A

echo refl a

{` refl of types is Id `}

axiom a0 : A

axiom a1 : A

echo Id A a0 a1

{` refl of functions is ap `}

axiom C : Type

axiom f : A → C

echo refl f

{` refl of type families is also Id `}

axiom B : A → Type

echo Id B

axiom a2 : A

{` refl of canonical types is ⁽ᵉ⁾ `}

def Unit : Type ≔ sig ()

axiom u0 : Unit

axiom u1 : Unit

echo Id Unit u0 u1
