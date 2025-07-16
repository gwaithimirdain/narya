{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

axiom A : Type
axiom B : Type
axiom R : A → B → Type
axiom Rb : isBisim A B R

axiom a : A

def glue.trr : Id B (glue A B R Rb .trr a) (Rb .trr a) ≔ refl _

def glue.liftr
  : Id (R a (glue A B R Rb .trr a)) (glue A B R Rb .liftr a .unglue)
      (Rb .liftr a)
  ≔ refl _

axiom b : B

def glue.trl : Id A (glue A B R Rb .trl b) (Rb .trl b) ≔ refl _

def glue.liftl
  : Id (R (glue A B R Rb .trl b) b) (glue A B R Rb .liftl b .unglue)
      (Rb .liftl b)
  ≔ refl _
