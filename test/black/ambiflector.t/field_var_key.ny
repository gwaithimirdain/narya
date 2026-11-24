def N : Type ≔ data [ zero. | suc. (_ : N) ]
def C : Type ≔ codata [ (x :♮| _) .fld : N ]
def D : Type ≔ sig ( y : C )
axiom d : D
def T : Type ≔ sig ( x : C, p : Id N ((x :♮| _) .fld) ((x :♮| _) .fld), q : Id N ((d .y :♮| _) .fld) ((d .y :♮| _) .fld), r : Id (Id N ((x :♮| _) .fld) ((x :♮| _) .fld)) p q )
