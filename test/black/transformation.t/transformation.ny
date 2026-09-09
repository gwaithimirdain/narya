{` -*- narya-prog-args: ("-proofgeneral" "-transformation") -*- `}

def ○ (A :○| DomMode) : CodMode ≔ data [ circle. (_ :○| A) ]
def ▱ (A :▱| DomMode) : CodMode ≔ data [ box. (_ :▱| A) ]

` The 2-cell alpha : ○ ⇒ ▱ induces a function ○ A → ▱ A for every A, relocking the
` ○-locked field of ○ A as the ▱-locked field of ▱ A.
def induced (A :○| DomMode) (u : ○ A) : ▱ A ≔ match u [ circle. x ↦ box. x ]
