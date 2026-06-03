{` -*- narya-prog-args: ("-proofgeneral" "-functor") -*- `}

def ○ (A :○| DomType) : CodType ≔ data [ circle. (_ :○| A) ]

def ○map (A B :○| DomType) (f :○| A → B) : ○ A → ○ B ≔ [
| circle. x ↦ circle. (f x)]
