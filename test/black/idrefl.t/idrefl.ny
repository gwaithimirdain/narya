axiom X : Type
axiom x0 : X
axiom x1 : X
axiom x2 : Id X x0 x1

{`Identity types are equivalently instantiations of refl of a type `}
def equiv_id : Id Type (Id X x0 x1) (refl X x0 x1) ≔ refl (Id X x0 x1)

{`We also have a standard degeneracy notation`}
def equiv_id' : Id Type (Id X x0 x1) (X⁽ᵉ⁾ x0 x1) ≔ refl (Id X x0 x1)

{`The identity function acts as the identity`}
def id_map_act : Id X (((x ↦ x) : X → X) x0) x0 ≔ refl x0

{`refl of the identity function acts as the identity on identifications`}
def refl_id_map_act : Id (Id X x0 x1) (refl ((x ↦ x) : (X → X)) x2) x2
  ≔ refl x2

{``}
axiom Y : Type
axiom Z : Type
axiom f : X → Y
axiom g : Y → Z
def gof : X → Z ≔ x ↦ g (f x)

{`Identity types of pi-types don't *compute* to the expected thing, but they are isomorphic, by eta-expansion in both directions.`}
axiom f' : X → Y
def idff : Type ≔ Id (X → Y) f f'
def idff' : Type ≔ (x : X) (x' : X) (x'' : Id X x x') → Id Y (f x) (f' x')

def idff_to_idff' : idff → idff' ≔ h x x' x'' ↦ h x''
def idff'_to_idff : idff' → idff ≔ k {x} {x'} x'' ↦ k x x' x''

def idff_roundtrip : (p : idff) → Id idff (idff'_to_idff (idff_to_idff' p)) p
  ≔ p ↦ refl p

def idff'_roundtrip
  : (q : idff') → Id idff' (idff_to_idff' (idff'_to_idff q)) q
  ≔ q ↦ refl q

{`Identity types are invariant under eta-expansion`}
def idff_eta : Type ≔ Id (X → Y) (x ↦ f x) (f')
def id_inv_under_eta : Id Type idff idff_eta ≔ refl idff

{`Ap is functorial`}
def ap_is_functorial
  : Id (Id Z (g (f x0)) (g (f x1))) (refl g (refl f x2))
      (refl ((x ↦ g (f x)) : X → Z) x2)
  ≔ refl (refl ((x ↦ g (f x)) : X → Z) x2)

{`The two degenerate squares associated to an identification have unequal types, although each has a standard degeneracy notation.`}
def r1x2 ≔ refl x2
def r1x2' ≔ x2⁽¹ᵉ⁾
def r1x2_eq_r1x2' : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x1) x2 x2) r1x2 r1x2'
  ≔ refl r1x2

def r2x2 ≔ (refl ((x ↦ refl x) : (x : X) → Id X x x) x2)
def r2x2' ≔ x2⁽ᵉ¹⁾
def r2x2_eq_r2x2' : Id (X⁽ᵉᵉ⁾ x2 x2 (refl x0) (refl x1)) r2x2 r2x2'
  ≔ refl r2x2

{`But applying symmetry identifies both their types and values.`}
def sr1x2_eq_r2x2 : Id (X⁽ᵉᵉ⁾ x2 x2 (refl x0) (refl x1)) (sym r1x2) r2x2
  ≔ refl r2x2

def sr1x2'_eq_r2x2' : Id (X⁽ᵉᵉ⁾ x2 x2 (refl x0) (refl x1)) (x2⁽ᵉ⁾⁽²¹⁾) r2x2'
  ≔ refl r2x2'

{`But the two degenerate squares associated to a reflexivity *are* equal.`}
def r1reflx0 ≔ refl (refl x0)
def r2reflx0 ≔ refl ((x ↦ refl x) : (x : X) → Id X x x) (refl x0)
def r1reflx0_eq_r2reflx0
  : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x0) (refl x0) (refl x0)) r1reflx0 r2reflx0
  ≔ refl r1reflx0

def r1reflx0' ≔ x0⁽ᵉᵉ⁾
def r1reflx0_eq_r1reflx0'
  : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x0) (refl x0) (refl x0)) r1reflx0 r1reflx0'
  ≔ refl r1reflx0

{`Doubly-degenerate squares are also fixed by symmetry`}
def sr1reflx0 ≔ sym (refl (refl x0))
def r1reflx0_eq_sr1reflx0
  : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x0) (refl x0) (refl x0)) r1reflx0 sr1reflx0
  ≔ refl r1reflx0
