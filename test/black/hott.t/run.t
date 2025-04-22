  $ narya -hott hott.ny
  A₂ .trr.1
    : A₀ → A₁
  
  A₂ .trl.1
    : A₁ → A₀
  
  A₂ .liftr.1
    : (x₀ : A₀) → A₂ x₀ (A₂ .trr.1 x₀)
  
  A₂ .liftl.1
    : (x₁ : A₁) → A₂ (A₂ .trl.1 x₁) x₁
  
  A₂ .trr.1 a₀
    : A₁
  
  A₂ .liftr.1 a₀
    : A₂ a₀ (A₂ .trr.1 a₀)
  
  A₂ .trl.1 a₁
    : A₀
  
  A₂ .liftl.1 a₁
    : A₂ (A₂ .trl.1 a₁) a₁
  
