  $ narya -v idrefl.ny
   ￫ info[I0001]
   ￮ axiom X assumed
  
   ￫ info[I0001]
   ￮ axiom x0 assumed
  
   ￫ info[I0001]
   ￮ axiom x1 assumed
  
   ￫ info[I0001]
   ￮ axiom x2 assumed
  
   ￫ info[I0000]
   ￮ constant equiv_id defined
  
   ￫ info[I0000]
   ￮ constant equiv_id' defined
  
   ￫ info[I0000]
   ￮ constant id_map_act defined
  
   ￫ info[I0000]
   ￮ constant refl_id_map_act defined
  
   ￫ info[I0001]
   ￮ axiom Y assumed
  
   ￫ info[I0001]
   ￮ axiom Z assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0000]
   ￮ constant gof defined
  
   ￫ info[I0001]
   ￮ axiom f' assumed
  
   ￫ info[I0000]
   ￮ constant idff defined
  
   ￫ info[I0000]
   ￮ constant idff' defined
  
   ￫ info[I0000]
   ￮ constant idff_to_idff' defined
  
   ￫ info[I0000]
   ￮ constant idff'_to_idff defined
  
   ￫ info[I0000]
   ￮ constant idff_roundtrip defined
  
   ￫ info[I0000]
   ￮ constant idff'_roundtrip defined
  
   ￫ info[I0000]
   ￮ constant idff_eta defined
  
   ￫ info[I0000]
   ￮ constant id_inv_under_eta defined
  
   ￫ info[I0000]
   ￮ constant ap_is_functorial defined
  
   ￫ info[I0000]
   ￮ constant r1x2 defined
  
   ￫ info[I0000]
   ￮ constant r1x2' defined
  
   ￫ info[I0000]
   ￮ constant r1x2_eq_r1x2' defined
  
   ￫ info[I0000]
   ￮ constant r2x2 defined
  
   ￫ info[I0000]
   ￮ constant r2x2' defined
  
   ￫ info[I0000]
   ￮ constant r2x2_eq_r2x2' defined
  
   ￫ info[I0000]
   ￮ constant sr1x2_eq_r2x2 defined
  
   ￫ info[I0000]
   ￮ constant sr1x2'_eq_r2x2' defined
  
   ￫ info[I0000]
   ￮ constant r1reflx0 defined
  
   ￫ info[I0000]
   ￮ constant r2reflx0 defined
  
   ￫ info[I0000]
   ￮ constant r1reflx0_eq_r2reflx0 defined
  
   ￫ info[I0000]
   ￮ constant r1reflx0' defined
  
   ￫ info[I0000]
   ￮ constant r1reflx0_eq_r1reflx0' defined
  
   ￫ info[I0000]
   ￮ constant sr1reflx0 defined
  
   ￫ info[I0000]
   ￮ constant r1reflx0_eq_sr1reflx0 defined
  
  $ narya idrefl.ny -e "def id_map_act' : Id X (((x ↦ x) : X → X) x0) x1 ≔ refl x1 synth (((x ↦ x) : X → X) x2)"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def id_map_act' : Id X (((x ↦ x) : X → X) x0) x1 ≔ refl x1 synth (((x ↦ x) : X → X) x2)
     ^ term synthesized type
         Id X x1 x1
       but is being checked against type
         Id X x0 x1
       unequal head constants:
         x1
       does not equal
         x0
  
  [1]
  $ narya idrefl.ny -e "synth (refl ((x ↦ x) : (X → X)) {x0} {x0} x2) synth (refl ((x ↦ x) : (X → X)) {x0} {x0} x0)"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | synth (refl ((x ↦ x) : (X → X)) {x0} {x0} x2) synth (refl ((x ↦ x) : (X → X)) {x0} {x0} x0)
     ^ term synthesized type
         Id X x0 x1
       but is being checked against type
         Id X x0 x0
       unequal head constants:
         x1
       does not equal
         x0
  
  [1]
  $ narya idrefl.ny -e "def gof' : X -> Z := x |-> f (g x) "
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def gof' : X -> Z := x |-> f (g x) 
     ^ term synthesized type
         X
       but is being checked against type
         Y
       unequal head constants:
         X
       does not equal
         Y
  
  [1]
  $ narya idrefl.ny -e "def idff_eq_idff' : Id Type idff idff' := refl idff"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def idff_eq_idff' : Id Type idff idff' := refl idff
     ^ term synthesized type
         Type⁽ᵉ⁾ ({H₀ : X} {H₁ : X} (H₂ : refl X H₀ H₁) ⇒ refl Y (f H₀) (f' H₁))
           ({H₀ : X} {H₁ : X} (H₂ : refl X H₀ H₁) ⇒ refl Y (f H₀) (f' H₁))
       but is being checked against type
         Type⁽ᵉ⁾ ({H₀ : X} {H₁ : X} (H₂ : refl X H₀ H₁) ⇒ refl Y (f H₀) (f' H₁))
           ((x : X) (x' : X) (x'' : refl X x x') → refl Y (f x) (f' x'))
       unequal head terms:
         Π⁽ᵉ⁾ (refl X) {_ ↦ Y} {_ ↦ Y} (_ ⤇ refl Y)
       does not equal
         (x : X) (x' : X) (x'' : refl X x x') → refl Y (f x) (f' x')
  
  [1]
  $ narya idrefl.ny -e "synth (refl g x2)"
   ￫ error[E0704]
   ￭ command-line exec string
   1 | synth (refl g x2)
     ^ the 0-boundary synthesized type
         X
       but is being checked against type
         Y
       unequal head constants:
         X
       does not equal
         Y
  
  [1]
