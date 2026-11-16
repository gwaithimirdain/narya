axiom A : Type
axiom g : (F : Type → Type) → F (F (F (F (F (F (F (F (F (F (F (F A)))))))))))
def h ≔ g (X ↦ X → X → X)
