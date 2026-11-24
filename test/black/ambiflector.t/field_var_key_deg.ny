def N : Type ≔ data [ zero. | suc. (_ : N) ]

def C : Type ≔ codata [ (x :♮| _) .fld : N ]

def T : Type ≔ sig (
  x : C,
  p : N⁽ᵉᵉᵉ⁾ ((refl (refl x) :♮| _) .fld) ((refl (refl x) :♮| _) .fld)
        ((refl (refl x) :♮| _) .fld) ((refl (refl x) :♮| _) .fld)
        ((refl (refl x) :♮| _) .fld) ((refl (refl x) :♮| _) .fld) )

def T' (x : N) : Type ≔ sig (
  x : C,
  p : N⁽ᵉᵉᵉ⁾ ((refl (refl x) :♮| _) .fld) ((refl (refl x) :♮| _) .fld)
        ((refl (refl x) :♮| _) .fld) ((refl (refl x) :♮| _) .fld)
        ((refl (refl x) :♮| _) .fld) ((refl (refl x) :♮| _) .fld) )
