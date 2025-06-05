  $ narya -hott tr.ny
  A₂ .trr
    : A₀ → A₁
  
  A₂ .trl
    : A₁ → A₀
  
  A₂ .liftr
    : (x₀ : A₀) → A₂ x₀ (A₂ .trr x₀)
  
  A₂ .liftl
    : (x₁ : A₁) → A₂ (A₂ .trl x₁) x₁
  
  A₂ .trr a₀
    : A₁
  
  A₂ .liftr a₀
    : A₂ a₀ (A₂ .trr a₀)
  
  A₂ .trl a₁
    : A₀
  
  A₂ .liftl a₁
    : A₂ (A₂ .trl a₁) a₁
  

  $ narya -hott tr2.ny
  A22 .trr.1
    : {H₀ : A00} {H₁ : A01} (H₂ : A02 H₀ H₁) ⇒ A12 (A20 .trr H₀) (A21 .trr H₁)
  
  A22 .trr.1 a02
    : A12 (A20 .trr a00) (A21 .trr a01)
  
  A20 .trr a00
    : A10
  
  A21 .trr a01
    : A11
  
  A22 .liftr.1
    : {x₀₀ : A00} {x₀₁ : A01} (x₀₂ : A02 x₀₀ x₀₁)
      ⇒ A22 x₀₂ (A22 .trr.1 x₀₂) (A20 .liftr x₀₀) (A21 .liftr x₀₁)
  
  A22 .liftr.1 a02
    : A22 a02 (A22 .trr.1 a02) (A20 .liftr a00) (A21 .liftr a01)
  
  A20 .liftr a00
    : A20 a00 (A20 .trr a00)
  
  A21 .liftr a01
    : A21 a01 (A21 .trr a01)
  
  A22 .trl.1
    : {H₀ : A10} {H₁ : A11} (H₂ : A12 H₀ H₁) ⇒ A02 (A20 .trl H₀) (A21 .trl H₁)
  
  A22 .trl.1 a12
    : A02 (A20 .trl a10) (A21 .trl a11)
  
  A20 .trl a10
    : A00
  
  A21 .trl a11
    : A01
  
  A22 .trr.2
    : {H₀ : A00} {H₁ : A10} (H₂ : A20 H₀ H₁) ⇒ A21 (A02 .trr H₀) (A12 .trr H₁)
  
  A22 .trr.2 a20
    : A21 (A02 .trr a00) (A12 .trr a10)
  
  sym A22 .trr.1 a20
    : A21 (A02 .trr a00) (A12 .trr a10)
  
  A02 .trr a00
    : A01
  
  A12 .trr a10
    : A11
  
  A22 .liftr.2
    : {x₀₀ : A00} {x₀₁ : A10} (x₀₂ : A20 x₀₀ x₀₁)
      ⇒ sym A22 x₀₂ (sym A22 .trr.1 x₀₂) (A02 .liftr x₀₀) (A12 .liftr x₀₁)
  
  A22 .liftr.2 a20
    : sym A22 a20 (sym A22 .trr.1 a20) (A02 .liftr a00) (A12 .liftr a10)
  
  sym A22 .liftr.1 a20
    : sym A22 a20 (sym A22 .trr.1 a20) (A02 .liftr a00) (A12 .liftr a10)
  
  sym A22 .trr.1 a20
    : A21 (A02 .trr a00) (A12 .trr a10)
  
  A02 .trr a00
    : A01
  
  A12 .trr a10
    : A11
  
  A02 .liftr a00
    : A02 a00 (A02 .trr a00)
  
  A12 .liftr a10
    : A12 a10 (A12 .trr a10)
  
  A22 a02 a12 .trr
    : A20 a00 a10 → A21 a01 a11
  
  A22 a02 a12 .trr a20
    : A21 a01 a11
  
  A22 a02 a12 .liftr a20
    : A22 a02 a12 a20 (A22 a02 a12 .trr a20)
  
  A22 a02 a12 .trl
    : A21 a01 a11 → A20 a00 a10
  
  A22 a02 a12 .trl a21
    : A20 a00 a10
  
  A22 a02 a12 .liftl a21
    : A22 a02 a12 (A22 a02 a12 .trl a21) a21
  
  sym A22 a20 a21 .trr
    : A02 a00 a01 → A12 a10 a11
  
  sym A22 a20 a21 .trr a02
    : A12 a10 a11
  
  sym (sym A22 a20 a21 .liftr a02)
    : A22 a02 (sym A22 a20 a21 .trr a02) a20 a21
  
  sym A22 a20 a21 .trl
    : A12 a10 a11 → A02 a00 a01
  
  sym A22 a20 a21 .trl a12
    : A02 a00 a01
  
  sym (sym A22 a20 a21 .liftl a12)
    : A22 (sym A22 a20 a21 .trl a12) a12 a20 a21
  

  $ narya -hott -v J.ny
   ￫ info[I0000]
   ￮ constant transport defined
  
   ￫ info[I0000]
   ￮ constant concat defined
  
   ￫ info[I0000]
   ￮ constant inverse defined
  
   ￫ info[I0000]
   ￮ constant transport2 defined
  
   ￫ info[I0000]
   ￮ constant refl_transport_1 defined
  
   ￫ info[I0000]
   ￮ constant refl_transport_2 defined
  
   ￫ info[I0000]
   ￮ constant Id2 defined
  
   ￫ info[I0000]
   ￮ constant concat_p1 defined
  
   ￫ info[I0000]
   ￮ constant J defined
  
   ￫ info[I0000]
   ￮ constant Sq defined
  
   ￫ info[I0000]
   ￮ constant conn defined
  
   ￫ info[I0000]
   ￮ constant coconn defined
  
   ￫ info[I0000]
   ￮ constant concat_1p defined
  
   ￫ info[I0000]
   ￮ constant Jβ defined
  

  $ narya -hott -v univalence.ny
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant isContr defined
  
   ￫ info[I0000]
   ￮ constant iscontr_idfrom defined
  
   ￫ info[I0000]
   ￮ constant is11 defined
  
   ￫ info[I0000]
   ￮ constant is11_Id defined
  
   ￫ info[I0000]
   ￮ constant bisim_of_11 defined
  
   ￫ info[I0000]
   ￮ constant univalence defined
  

  $ narya -hott pi.ny
  B₂ (A₂ .liftl a₁) .trr (f₀ (A₂ .trl a₁))
    : B₁ a₁
  
  B₂ (A₂ .liftl a₁) .trr (f₀ (A₂ .trl a₁))
    : B₁ a₁
  
  B₂ (A₂ .liftr a₀) .trl (f₁ (A₂ .trr a₀))
    : B₀ a₀
  
  B₂ (A₂ .liftr a₀) .trl (f₁ (A₂ .trr a₀))
    : B₀ a₀
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl a₁) .liftl (refl a₁)))
      (refl f₀ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl a₁) .trl (refl a₁)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftl.1 (refl a₁))
       .trr.1 (refl f₀ (A₂⁽¹ᵉ⁾ .trl.1 (refl a₁))))
    .trl (B₂ (A₂ .liftl a₁) .liftr (f₀ (A₂ .trl a₁)))
    : B₂ a₂ (f₀ a₀) (B₂ (A₂ .liftl a₁) .trr (f₀ (A₂ .trl a₁)))
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl a₁) .liftl (refl a₁)))
      (ap f₀ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl a₁) .trl (refl a₁)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftl.1 (refl a₁))
       .trr.1 (ap f₀ (A₂⁽¹ᵉ⁾ .trl.1 (refl a₁))))
    .trl (B₂ (A₂ .liftl a₁) .liftr (f₀ (A₂ .trl a₁)))
    : B₂ a₂ (f₀ a₀) (B₂ (A₂ .liftl a₁) .trr (f₀ (A₂ .trl a₁)))
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr a₀) .liftr (refl a₀)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftr.1 (refl a₀))
       .trl.1 (refl f₁ (A₂⁽¹ᵉ⁾ .trr.1 (refl a₀))))
      (refl f₁ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr a₀) .trr (refl a₀)))
    .trl (B₂ (A₂ .liftr a₀) .liftl (f₁ (A₂ .trr a₀)))
    : B₂ a₂ (B₂ (A₂ .liftr a₀) .trl (f₁ (A₂ .trr a₀))) (f₁ a₁)
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr a₀) .liftr (refl a₀)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftr.1 (refl a₀))
       .trl.1 (ap f₁ (A₂⁽¹ᵉ⁾ .trr.1 (refl a₀))))
      (ap f₁ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr a₀) .trr (refl a₀)))
    .trl (B₂ (A₂ .liftr a₀) .liftl (f₁ (A₂ .trr a₀)))
    : B₂ a₂ (B₂ (A₂ .liftr a₀) .trl (f₁ (A₂ .trr a₀))) (f₁ a₁)
  

  $ narya -hott pi2.ny
  B22 (A22 (A02 .liftl a01) (A12 .liftl a11) .liftl a21) (f02 (A02 .liftl a01))
      (f12 (A12 .liftl a11))
    .trr (f20 (A22 (A02 .liftl a01) (A12 .liftl a11) .trl a21))
    : B21 a21 (f01 a01) (f11 a11)
  
  B22 (A22 (A02 .liftl a01) (A12 .liftl a11) .liftl a21) (f02 (A02 .liftl a01))
      (f12 (A12 .liftl a11))
    .trr (f20 (A22 (A02 .liftl a01) (A12 .liftl a11) .trl a21))
    : B21 a21 (f01 a01) (f11 a11)
  
  B22 (A22 (A02 .liftr a00) (A12 .liftr a10) .liftr a20) (f02 (A02 .liftr a00))
      (f12 (A12 .liftr a10))
    .trl (f21 (A22 (A02 .liftr a00) (A12 .liftr a10) .trr a20))
    : B20 a20 (f00 a00) (f10 a10)
  
  B22 (A22 (A02 .liftr a00) (A12 .liftr a10) .liftr a20) (f02 (A02 .liftr a00))
      (f12 (A12 .liftr a10))
    .trl (f21 (A22 (A02 .liftr a00) (A12 .liftr a10) .trr a20))
    : B20 a20 (f00 a00) (f10 a10)
  
  B22⁽¹²ᵉ⁾
      (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .liftl (refl a01)))
           (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11) .liftr a12)
           (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                (refl A10 .liftr a10)
            .liftr a20) (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21)
       .liftr a22)
      (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .liftl (refl a01))))
      (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11) .liftr a12))
      (refl f20
         (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
              (refl A10 .liftr a10)
          .liftr a20))
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01))
                (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr a11))
            .liftl.1 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21))
           (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01)))
           (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr a11)))
       .trr.1
         (refl f20
            (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01))
                 (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr a11))
             .trl.1 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21))))
    .trl
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                (sym
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                         .trr a12) (A12 .liftl (refl A11 .trr a11))
                    .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                     (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                           .trr a12) (A12 .liftl (refl A11 .trr a11))
                      .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                 .liftr
                   (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                        (refl A10 .liftr a10)
                    .trr a20))
                (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                 .liftr (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21))
            .liftr
              (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .liftl (refl a01)))
                   (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                    .liftr a12)
                   (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                        (refl A10 .liftr a10)
                    .liftr a20)
                   (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21)
               .trr a22)) (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
           (f12⁽¹ᵉ⁾
              (sym
                 (A12⁽ᵉ¹⁾
                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                       .trr a12) (A12 .liftl (refl A11 .trr a11))
                  .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))))
           (refl f20
              (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                         .trr a12) (A12 .liftl (refl A11 .trr a11))
                    .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
               .liftr
                 (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                      (refl A10 .liftr a10)
                  .trr a20)))
           (B22⁽¹²ᵉ⁾
                (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                     (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                 .liftl.1
                   (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                    .liftr (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21)))
                (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
                (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
            .trr.1
              (refl f20
                 (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                      (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                  .trl.1
                    (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                     .liftr (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21)))))
       .trl
         (B22⁽¹²ᵉ⁾
              (sym
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftl.1 (refl a01)))
                      (sym (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                        (refl A11 .liftr a11)
                                    .trr a12) (A12 .liftl (refl A11 .trr a11))
                               .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                           (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                          (refl A11 .liftr a11)
                                      .trr a12)
                                     (A12 .liftl (refl A11 .trr a11))
                                 .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                            .liftr
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                    .trl (refl a01)) (refl A10 .liftr a10)
                               .trr a20))
                           (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                            .liftr
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                               .trr a21))
                       .trr
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                  .liftl (refl a01)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                   (refl A11 .liftr a11)
                               .liftr a12)
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                    .trl (refl a01)) (refl A10 .liftr a10)
                               .liftr a20)
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                               .liftr a21)
                          .trr a22))
                      (A22 (A02 .liftl a01) (A12 .liftl (refl A11 .trr a11))
                       .liftl
                         (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                          .trr
                            (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21)))
                  .liftl
                    (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                     .trr.1
                       (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                        .trr.1 (refl a21)))))
              (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
              (f12⁽¹ᵉ⁾ (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
              (refl f20
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftl.1 (refl a01)))
                      (sym (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                        (refl A11 .liftr a11)
                                    .trr a12) (A12 .liftl (refl A11 .trr a11))
                               .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                           (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                          (refl A11 .liftr a11)
                                      .trr a12)
                                     (A12 .liftl (refl A11 .trr a11))
                                 .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                            .liftr
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                    .trl (refl a01)) (refl A10 .liftr a10)
                               .trr a20))
                           (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                            .liftr
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                               .trr a21))
                       .trr
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                  .liftl (refl a01)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                   (refl A11 .liftr a11)
                               .liftr a12)
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                    .trl (refl a01)) (refl A10 .liftr a10)
                               .liftr a20)
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                               .liftr a21)
                          .trr a22))
                      (A22 (A02 .liftl a01) (A12 .liftl (refl A11 .trr a11))
                       .liftl
                         (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                          .trr
                            (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21)))
                  .trl
                    (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                     .trr.1
                       (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                        .trr.1 (refl a21)))))
              (B22⁽¹²ᵉ⁾
                   (A22⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                        (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                    .liftl.1
                      (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                       .trr.1
                         (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                          .trr.1 (refl a21))))
                   (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
                   (f12⁽¹ᵉ⁾ (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
               .trr.1
                 (refl f20
                    (A22⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                         (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                     .trl.1
                       (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                        .trr.1
                          (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                           .trr.1 (refl a21))))))
          .trl
            (B22
                 (A22 (A02 .liftl a01) (A12 .liftl (refl A11 .trr a11))
                  .liftl
                    (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                     .trr (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21)))
                 (f02 (A02 .liftl a01)) (f12 (A12 .liftl (refl A11 .trr a11)))
             .liftr
               (f20
                  (A22 (A02 .liftl a01) (A12 .liftl (refl A11 .trr a11))
                   .trl
                     (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                      .trr (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21)))))))
    : B22 a22 (f02 a02) (f12 a12) (f20 a20)
        (B22 (A22 (A02 .liftl a01) (A12 .liftl a11) .liftl a21)
             (f02 (A02 .liftl a01)) (f12 (A12 .liftl a11))
         .trr (f20 (A22 (A02 .liftl a01) (A12 .liftl a11) .trl a21)))
  
  B22⁽¹²ᵉ⁾
      (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .liftr (refl a00)))
           (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11) .liftr a12)
           (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20)
           (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                (refl A11 .liftr a11)
            .liftr a21)
       .liftr a22)
      (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .liftr (refl a00))))
      (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11) .liftr a12))
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00))
                (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr a10))
            .liftr.1 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20))
           (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00)))
           (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr a10)))
       .trl.1
         (refl f21
            (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00))
                 (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr a10))
             .trr.1 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20))))
      (refl f21
         (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
              (refl A11 .liftr a11)
          .liftr a21))
    .trl
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                (sym
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                         .trr a12) (A12 .liftr (refl A10 .trr a10))
                    .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                 .liftr (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20))
                (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                     (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                           .trr a12) (A12 .liftr (refl A10 .trr a10))
                      .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                 .liftr
                   (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                        (refl A11 .liftr a11)
                    .trr a21))
            .liftr
              (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .liftr (refl a00)))
                   (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                    .liftr a12)
                   (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20)
                   (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                        (refl A11 .liftr a11)
                    .liftr a21)
               .trr a22)) (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
           (f12⁽¹ᵉ⁾
              (sym
                 (A12⁽ᵉ¹⁾
                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                       .trr a12) (A12 .liftr (refl A10 .trr a10))
                  .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))))
           (B22⁽¹²ᵉ⁾
                (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                     (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                 .liftr.1
                   (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                    .liftr (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20)))
                (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
                (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
            .trl.1
              (refl f21
                 (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                      (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                  .trr.1
                    (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                     .liftr (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20)))))
           (refl f21
              (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                         .trr a12) (A12 .liftr (refl A10 .trr a10))
                    .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
               .liftr
                 (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                      (refl A11 .liftr a11)
                  .trr a21)))
       .trl
         (B22⁽¹²ᵉ⁾
              (sym
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftr.1 (refl a00)))
                      (sym (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                        (refl A11 .liftr a11)
                                    .trr a12) (A12 .liftr (refl A10 .trr a10))
                               .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                           (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                            .liftr
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                               .trr a20))
                           (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                          (refl A11 .liftr a11)
                                      .trr a12)
                                     (A12 .liftr (refl A10 .trr a10))
                                 .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                            .liftr
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                    .trr (refl a00)) (refl A11 .liftr a11)
                               .trr a21))
                       .trr
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                  .liftr (refl a00)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                   (refl A11 .liftr a11)
                               .liftr a12)
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                               .liftr a20)
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                    .trr (refl a00)) (refl A11 .liftr a11)
                               .liftr a21)
                          .trr a22))
                      (A22 (A02 .liftr a00) (A12 .liftr (refl A10 .trr a10))
                       .liftr
                         (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                          .trr
                            (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20)))
                  .liftr
                    (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                     .trr.1
                       (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                        .trr.1 (refl a20)))))
              (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
              (f12⁽¹ᵉ⁾ (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
              (B22⁽¹²ᵉ⁾
                   (A22⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                        (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                    .liftr.1
                      (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                       .trr.1
                         (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                          .trr.1 (refl a20))))
                   (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
                   (f12⁽¹ᵉ⁾ (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
               .trl.1
                 (refl f21
                    (A22⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                         (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                     .trr.1
                       (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                        .trr.1
                          (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                           .trr.1 (refl a20))))))
              (refl f21
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftr.1 (refl a00)))
                      (sym (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                        (refl A11 .liftr a11)
                                    .trr a12) (A12 .liftr (refl A10 .trr a10))
                               .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                           (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                            .liftr
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                               .trr a20))
                           (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                          (refl A11 .liftr a11)
                                      .trr a12)
                                     (A12 .liftr (refl A10 .trr a10))
                                 .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                            .liftr
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                    .trr (refl a00)) (refl A11 .liftr a11)
                               .trr a21))
                       .trr
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                  .liftr (refl a00)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                   (refl A11 .liftr a11)
                               .liftr a12)
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                               .liftr a20)
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                    .trr (refl a00)) (refl A11 .liftr a11)
                               .liftr a21)
                          .trr a22))
                      (A22 (A02 .liftr a00) (A12 .liftr (refl A10 .trr a10))
                       .liftr
                         (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                          .trr
                            (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20)))
                  .trr
                    (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                     .trr.1
                       (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                        .trr.1 (refl a20)))))
          .trl
            (B22
                 (A22 (A02 .liftr a00) (A12 .liftr (refl A10 .trr a10))
                  .liftr
                    (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                     .trr (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20)))
                 (f02 (A02 .liftr a00)) (f12 (A12 .liftr (refl A10 .trr a10)))
             .liftl
               (f21
                  (A22 (A02 .liftr a00) (A12 .liftr (refl A10 .trr a10))
                   .trr
                     (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                      .trr (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20)))))))
    : B22 a22 (f02 a02) (f12 a12)
        (B22 (A22 (A02 .liftr a00) (A12 .liftr a10) .liftr a20)
             (f02 (A02 .liftr a00)) (f12 (A12 .liftr a10))
         .trl (f21 (A22 (A02 .liftr a00) (A12 .liftr a10) .trr a20))) (f21 a21)
  

  $ narya -hott sigma.ny
  refl Σ A₂ B₂ .trr u₀
    : Σ A₁ B₁
  
  A₂ .trr (u₀ .fst)
    : A₁
  
  A₂ .trr (u₀ .fst)
    : A₁
  
  B₂ (A₂ .liftr (u₀ .fst)) .trr (u₀ .snd)
    : B₁ (A₂ .trr (u₀ .fst))
  
  B₂ (A₂ .liftr (u₀ .fst)) .trr (u₀ .snd)
    : B₁ (A₂ .trr (u₀ .fst))
  
  refl Σ A₂ B₂ .liftr u₀
    : Σ⁽ᵉ⁾ A₂ B₂ u₀ (refl Σ A₂ B₂ .trr u₀)
  
  A₂ .liftr (u₀ .fst)
    : A₂ (u₀ .fst) (A₂ .trr (u₀ .fst))
  
  A₂ .liftr (u₀ .fst)
    : A₂ (u₀ .fst) (A₂ .trr (u₀ .fst))
  
  B₂ (A₂ .liftr (u₀ .fst)) .liftr (u₀ .snd)
    : B₂ (A₂ .liftr (u₀ .fst)) (u₀ .snd)
        (B₂ (A₂ .liftr (u₀ .fst)) .trr (u₀ .snd))
  
  B₂ (A₂ .liftr (u₀ .fst)) .liftr (u₀ .snd)
    : B₂ (A₂ .liftr (u₀ .fst)) (u₀ .snd)
        (B₂ (A₂ .liftr (u₀ .fst)) .trr (u₀ .snd))
  
  refl Σ A₂ B₂ .trl u₁
    : Σ A₀ B₀
  
  A₂ .trl (u₁ .fst)
    : A₀
  
  B₂ (A₂ .liftl (u₁ .fst)) .trl (u₁ .snd)
    : B₀ (A₂ .trl (u₁ .fst))
  
  refl Σ A₂ B₂ .liftl u₁
    : Σ⁽ᵉ⁾ A₂ B₂ (refl Σ A₂ B₂ .trl u₁) u₁
  
  A₂ .liftl (u₁ .fst)
    : A₂ (A₂ .trl (u₁ .fst)) (u₁ .fst)
  
  B₂ (A₂ .liftl (u₁ .fst)) .liftl (u₁ .snd)
    : B₂ (A₂ .liftl (u₁ .fst)) (B₂ (A₂ .liftl (u₁ .fst)) .trl (u₁ .snd))
        (u₁ .snd)
  

  $ narya -hott sigma2.ny
  A22 .trr.1 (u02 .fst)
    : A12 (A20 .trr (u00 .fst)) (A21 .trr (u01 .fst))
  
  sym A22 .trr.1 (u20 .fst)
    : A21 (A02 .trr (u00 .fst)) (A12 .trr (u10 .fst))
  
  Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trr u20
    : Σ⁽ᵉ⁾ A21 B21 u01 u11
  
  A22 (u02 .fst) (u12 .fst) .trr (u20 .fst)
    : A21 (u01 .fst) (u11 .fst)
  
  B22 (A22 (u02 .fst) (u12 .fst) .liftr (u20 .fst)) (u02 .snd) (u12 .snd)
    .trr (u20 .snd)
    : B21 (A22 (u02 .fst) (u12 .fst) .trr (u20 .fst)) (u01 .snd) (u11 .snd)
  
  Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftr u20
    : Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 u20 (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trr u20)
  
  A22 (u02 .fst) (u12 .fst) .liftr (u20 .fst)
    : A22 (u02 .fst) (u12 .fst) (u20 .fst)
        (A22 (u02 .fst) (u12 .fst) .trr (u20 .fst))
  
  B22 (A22 (u02 .fst) (u12 .fst) .liftr (u20 .fst)) (u02 .snd) (u12 .snd)
    .liftr (u20 .snd)
    : B22 (A22 (u02 .fst) (u12 .fst) .liftr (u20 .fst)) (u02 .snd) (u12 .snd)
        (u20 .snd)
        (B22 (A22 (u02 .fst) (u12 .fst) .liftr (u20 .fst)) (u02 .snd)
             (u12 .snd)
         .trr (u20 .snd))
  
  Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trl u21
    : Σ⁽ᵉ⁾ A20 B20 u00 u10
  
  A22 (u02 .fst) (u12 .fst) .trl (u21 .fst)
    : A20 (u00 .fst) (u10 .fst)
  
  B22 (A22 (u02 .fst) (u12 .fst) .liftl (u21 .fst)) (u02 .snd) (u12 .snd)
    .trl (u21 .snd)
    : B20 (A22 (u02 .fst) (u12 .fst) .trl (u21 .fst)) (u00 .snd) (u10 .snd)
  
  Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .liftl u21
    : Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 .trl u21) u21
  
  A22 (u02 .fst) (u12 .fst) .liftl (u21 .fst)
    : A22 (u02 .fst) (u12 .fst) (A22 (u02 .fst) (u12 .fst) .trl (u21 .fst))
        (u21 .fst)
  
  B22 (A22 (u02 .fst) (u12 .fst) .liftl (u21 .fst)) (u02 .snd) (u12 .snd)
    .liftl (u21 .snd)
    : B22 (A22 (u02 .fst) (u12 .fst) .liftl (u21 .fst)) (u02 .snd) (u12 .snd)
        (B22 (A22 (u02 .fst) (u12 .fst) .liftl (u21 .fst)) (u02 .snd)
             (u12 .snd)
         .trl (u21 .snd)) (u21 .snd)
  

  $ narya -hott 3sigma.ny
  refl Σ3 A₂ B₂ C₂ .trr u₀
    : Σ3 A₁ B₁ C₁
  
  A₂ .trr (u₀ .fst)
    : A₁
  
  B₂ (A₂ .liftr (u₀ .fst)) .trr (u₀ .snd)
    : B₁ (A₂ .trr (u₀ .fst))
  
  C₂ (A₂ .liftr (u₀ .fst)) (B₂ (A₂ .liftr (u₀ .fst)) .liftr (u₀ .snd))
    .trr (u₀ .thd)
    : C₁ (A₂ .trr (u₀ .fst)) (B₂ (A₂ .liftr (u₀ .fst)) .trr (u₀ .snd))
  
  refl Σ3 A₂ B₂ C₂ .liftr u₀
    : Σ3⁽ᵉ⁾ A₂ B₂ C₂ u₀ (refl Σ3 A₂ B₂ C₂ .trr u₀)
  
  A₂ .liftr (u₀ .fst)
    : A₂ (u₀ .fst) (A₂ .trr (u₀ .fst))
  
  B₂ (A₂ .liftr (u₀ .fst)) .liftr (u₀ .snd)
    : B₂ (A₂ .liftr (u₀ .fst)) (u₀ .snd)
        (B₂ (A₂ .liftr (u₀ .fst)) .trr (u₀ .snd))
  
  C₂ (A₂ .liftr (u₀ .fst)) (B₂ (A₂ .liftr (u₀ .fst)) .liftr (u₀ .snd))
    .liftr (u₀ .thd)
    : C₂ (A₂ .liftr (u₀ .fst)) (B₂ (A₂ .liftr (u₀ .fst)) .liftr (u₀ .snd))
        (u₀ .thd)
        (C₂ (A₂ .liftr (u₀ .fst)) (B₂ (A₂ .liftr (u₀ .fst)) .liftr (u₀ .snd))
         .trr (u₀ .thd))
  

  $ narya -hott prod.ny
  refl prod A₂ B₂ .trr u₀
    : prod A₁ B₁
  
  A₂ .trr (u₀ .fst)
    : A₁
  
  B₂ .trr (u₀ .snd)
    : B₁
  
  refl prod A₂ B₂ .liftr u₀
    : prod⁽ᵉ⁾ A₂ B₂ u₀ (refl prod A₂ B₂ .trr u₀)
  
  A₂ .liftr (u₀ .fst)
    : A₂ (u₀ .fst) (A₂ .trr (u₀ .fst))
  
  B₂ .liftr (u₀ .snd)
    : B₂ (u₀ .snd) (B₂ .trr (u₀ .snd))
  

  $ narya -hott m.ny
  refl M A₂ B₂ .trr u₀
    : M A₁ B₁
  
  A₂ .trr (u₀ .recv)
    : A₁
  
  refl M A₂ B₂ .trr (u₀ .send (B₂ (A₂ .liftr (u₀ .recv)) .trl b₁))
    : M A₁ B₁
  
  refl M A₂ B₂ .liftr u₀
    : M⁽ᵉ⁾ A₂ B₂ u₀ (refl M A₂ B₂ .trr u₀)
  
  A₂ .liftr (u₀ .recv)
    : A₂ (u₀ .recv) (A₂ .trr (u₀ .recv))
  
  M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
      (refl u₀
       .send
         (B₂⁽ᵉ¹⁾ (sym (refl A₂ .liftr.1 (refl u₀ .recv))) b₂
              (B₂ (A₂ .liftr (u₀ .recv)) .liftl b₁)
          .trl (refl b₁)))
      (M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
       .trr.1
         (refl u₀
          .send (B₂⁽¹ᵉ⁾ (refl A₂ .liftr.1 (refl u₀ .recv)) .trl.1 (refl b₁))))
    .trl (refl M A₂ B₂ .liftr (u₀ .send (B₂ (A₂ .liftr (u₀ .recv)) .trl b₁)))
    : M⁽ᵉ⁾ A₂ B₂ (u₀ .send b₀)
        (refl M A₂ B₂ .trr (u₀ .send (B₂ (A₂ .liftr (u₀ .recv)) .trl b₁)))
  
  M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
      (refl u₀
       .send
         (B₂⁽ᵉ¹⁾ (sym (A₂⁽ᵉ⁾ .liftr.1 (refl u₀ .recv))) b₂
              (B₂ (A₂ .liftr (u₀ .recv)) .liftl b₁)
          .trl (refl b₁)))
      (M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
       .trr.1
         (refl u₀
          .send (B₂⁽¹ᵉ⁾ (A₂⁽ᵉ⁾ .liftr.1 (refl u₀ .recv)) .trl.1 (refl b₁))))
    .trl (M⁽ᵉ⁾ A₂ B₂ .liftr (u₀ .send (B₂ (A₂ .liftr (u₀ .recv)) .trl b₁)))
    : M⁽ᵉ⁾ A₂ B₂ (u₀ .send b₀)
        (refl M A₂ B₂ .trr (u₀ .send (B₂ (A₂ .liftr (u₀ .recv)) .trl b₁)))
  
