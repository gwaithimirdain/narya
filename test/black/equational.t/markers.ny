import "equational"

def keep (a b : Id A z y) : Id A z y ≔ a

notation(0) a "<-" b ≔ keep a b

def application : Id A x z ≔ calc
  x
  = x
  = y
      by p
  = y
  = z
      by ← keep s s
  = z ∎

def application_def : Id (Id A x z) application xz' ≔ refl application

def nested : Id A x z ≔ calc
  x
  = y
      by p
  = z
      by ← (calc
              z
              = y
                  by s ∎) ∎

def infix : Id A x z ≔ calc
  x
  = y
      by p
  = z
      by ← s <- s ∎

def infix_def : Id (Id A x z) infix xz' ≔ refl infix

def ← : Id A x y ≔ p

def ←p : Id A x y ≔ p

def arrow_identifier : Id A x y ≔ calc
  x
  = y
      by (←) ∎

def joined_identifier : Id A x y ≔ calc
  x
  = y
      by ←p ∎
