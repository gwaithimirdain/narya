{` -*- narya-prog-args: ("-proofgeneral" "-composable-transformations") -*- `}

def ○ (A :○| DomMode) : CodMode ≔ data [ circle. (_ :○| A) ]
def ▱ (A :▱| DomMode) : CodMode ≔ data [ box. (_ :▱| A) ]
def ▷ (A :▷| DomMode) : CodMode ≔ data [ tri. (_ :▷| A) ]

` The two generating 2-cells, alpha : ○ ⇒ ▱ and beta : ▱ ⇒ ▷, each induce a function by
` relocking the field.
def alpha_map (A :○| DomMode) (u : ○ A) : ▱ A ≔ match u [ circle. x ↦ box. x ]
def beta_map (A :▱| DomMode) (u : ▱ A) : ▷ A ≔ match u [ box. x ↦ tri. x ]

` There is no separate generator for the composite ○ ⇒ ▷; since the theory is locally posetal,
` the vertical composite beta ∘ alpha is automatically the unique such cell, and it induces this
` function directly.
def gamma_map (A :○| DomMode) (u : ○ A) : ▷ A ≔ match u [ circle. x ↦ tri. x ]

` Composing alpha_map and beta_map agrees with gamma_map.
def composed (A :○| DomMode) (u : ○ A) : ▷ A ≔ beta_map A (alpha_map A u)

def composed_ok (A :○| DomMode) (u : ○ A) : Id (▷ A) (composed A u) (gamma_map A u) ≔
  match u [ circle. x ↦ refl (tri. x) ]
