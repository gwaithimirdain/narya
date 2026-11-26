def lconn_data (A : Type) (a0 a1 : A) (a2 : Id A a0 a1) : Type := sig (
lconn : A⁽ᵉᵉ⁾ (refl a0) a2 (refl a0) a2,
a2ish : Id A a0 a1,
lconnish : A⁽ᵉᵉ⁾ (refl a0) a2 (refl a0) a2ish,
cube : A⁽ᵉᵉᵉ⁾ a0⁽ᵉᵉ⁾ lconnish a0⁽ᵉᵉ⁾ lconnish a0⁽ᵉᵉ⁾ lconn
)
