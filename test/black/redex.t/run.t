  $ narya redex.ny
  (x ↦ f x) a
    : B a
  
  f a
    : B a
  
  (x ↦ ()) a
    : unit
  
  ()
    : unit
  
  ap (x ↦ f x) a₂
    : Id B a₂ (f a₀) (f a₁)
  
  ap f a₂
    : Id B a₂ (f a₀) (f a₁)
  
  ap (x ↦ ()) a₂
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  
  (x ↦ f x)⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ a22 (ap f a02) (ap f a12) (ap f a20) (ap f a21)
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ a22 (ap f a02) (ap f a12) (ap f a20) (ap f a21)
  
  (x ↦ ())⁽ᵉᵉ⁾ a22
    : unit⁽ᵉᵉ⁾ {()} {()} () {()} {()} () () ()
  
  ()
    : unit⁽ᵉᵉ⁾ {()} {()} () {()} {()} () () ()
  
  (x y ↦ g x y) a ()
    : B a
  
  g a ()
    : B a
  
  (x y ↦ ()) a ()
    : unit
  
  ()
    : unit
  
  (y x ↦ g x y) () a
    : B a
  
  g a ()
    : B a
  
  (y x ↦ ()) () a
    : unit
  
  ()
    : unit
  
  ap (x y ↦ g x y) a₂ {()} {()} ()
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  ap g a₂ {()} {()} ()
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  ap (y x ↦ g x y) {()} {()} () a₂
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  ap g a₂ {()} {()} ()
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  ap (x y ↦ ()) a₂ {()} {()} ()
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  
  ap (y x ↦ ()) {()} {()} () a₂
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  
  (x y ↦ h x y) a ()
    : B a
  
  h a ()
    : B a
  
  (x y ↦ ()) a ()
    : unit
  
  ()
    : unit
  
  ap (x y ↦ h x y) a₂ {()} {()} ()
    : Id B a₂ (h a₀ ()) (h a₁ ())
  
  ap h a₂ {()} {()} ()
    : Id B a₂ (h a₀ ()) (h a₁ ())
  
  ap (x y ↦ ()) a₂ {()} {()} ()
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  

