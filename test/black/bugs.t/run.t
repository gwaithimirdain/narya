  $ narya -v issue69.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0000]
   ￮ constant D defined
  
   ￫ info[I0000]
   ￮ constant get_a defined
  
   ￫ info[I0000]
   ￮ constant get_f defined
  

  $ narya issue84.ny
  (Id A ⇒ Id B) .trr
    : (A → B) → A → B
  
  a1 ↦ refl B .trr (f (refl A .trl a1))
    : A → B
  
  (Id A ⇒ Id B) .liftr
    : (x₀ : A → B)
      → {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁)
        →⁽ᵉ⁾ Id B (x₀ 𝑥₀) (refl B .trr (x₀ (refl A .trl 𝑥₁)))
  
  a ⤇
  B⁽ᵉᵉ⁾ (refl f (A⁽ᵉᵉ⁾ a.2 (refl A .liftl a.1) .trl (refl a.1)))
      (B⁽ᵉᵉ⁾ .trr.1 (refl f (A⁽ᵉᵉ⁾ .trl.1 (refl a.1))))
  .trl (refl B .liftr (f (refl A .trl a.1)))
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁)
      →⁽ᵉ⁾ Id B (f 𝑥₀) (refl B .trr (f (refl A .trl 𝑥₁)))
  
  (Id A ⇒ Id B) .trl
    : (A → B) → A → B
  
  a0 ↦ refl B .trl (f (refl A .trr a0))
    : A → B
  
  (Id A ⇒ Id B) .liftl
    : (x₁ : A → B)
      → {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁)
        →⁽ᵉ⁾ Id B (refl B .trl (x₁ (refl A .trr 𝑥₀))) (x₁ 𝑥₁)
  
  a ⤇
  B⁽ᵉᵉ⁾ (B⁽ᵉᵉ⁾ .trl.1 (refl f (A⁽ᵉᵉ⁾ .trr.1 (refl a.0))))
      (refl f (A⁽ᵉᵉ⁾ a.2 (refl A .liftr a.0) .trr (refl a.0)))
  .trl (refl B .liftl (f (refl A .trr a.0)))
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁)
      →⁽ᵉ⁾ Id B (refl B .trl (f (refl A .trr 𝑥₀))) (f 𝑥₁)
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .trr
    : ({𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁))
      → {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁)
  
  a ⤇
  B⁽ᵉᵉ⁾ (refl f (refl A .liftl a.0)) (refl f (refl A .liftl a.1))
  .trr (refl f (A⁽ᵉᵉ⁾ (refl A .liftl a.0) (refl A .liftl a.1) .trl a.2))
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁)
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .liftr
    : (x₀ : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁))
      → {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
        {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
        (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (x₀ 𝑥₂₀)
                (B⁽ᵉᵉ⁾ (refl f (refl A .liftl 𝑥₀₁))
                     (refl f (refl A .liftl 𝑥₁₁))
                 .trr
                   (x₀
                      (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₁) (refl A .liftl 𝑥₁₁) .trl 𝑥₂₁)))
  
  a ⤇
  B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (sym (A⁽ᵉᵉ⁾ a.02 (refl A .liftl a.01) .liftl (refl a.01))))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11) .liftr a.12))
      (f⁽ᵉᵉ⁾
         (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ a.02 (refl A .liftl a.01) .trl (refl a.01))
              (refl A .liftr a.10)
          .liftr a.20))
      (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01)))
           (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl A .liftr a.11)))
       .trr.1
         (f⁽ᵉᵉ⁾
            (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01))
                 (A⁽ᵉᵉ⁾ .liftl.1 (refl A .liftr a.11))
             .trl.1 (A⁽ᵉᵉ⁾ (refl a.01) (refl A .liftr a.11) .liftr a.21))))
  .trl
    (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01)))
         (f⁽ᵉᵉ⁾
            (sym
               (A⁽ᵉᵉ⁾
                    (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11)
                     .trr a.12) (refl A .liftl (refl A .trr a.11))
                .liftl (A⁽ᵉᵉ⁾ .trr.1 (refl a.11)))))
         (f⁽ᵉᵉ⁾
            (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .trl.1 (refl a.01))
                 (A⁽ᵉᵉ⁾
                      (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11)
                       .trr a.12) (refl A .liftl (refl A .trr a.11))
                  .trl (A⁽ᵉᵉ⁾ .trr.1 (refl a.11)))
             .liftr
               (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ a.02 (refl A .liftl a.01) .trl (refl a.01))
                    (refl A .liftr a.10)
                .trr a.20)))
         (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01)))
              (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))))
          .trr.1
            (f⁽ᵉᵉ⁾
               (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01))
                    (A⁽ᵉᵉ⁾ .liftl.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.11)))
                .trl.1
                  (A⁽ᵉᵉ⁾ (refl a.01) (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))
                   .liftr (A⁽ᵉᵉ⁾ (refl a.01) (refl A .liftr a.11) .trr a.21)))))
     .trl
       (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01)))
            (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))))
            (f⁽ᵉᵉ⁾
               (A⁽ᵉᵉᵉ⁾ (sym (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01)))
                    (sym (A⁽ᵉᵉ⁾ .liftl.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))))
                    (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01))
                         (sym
                            (A⁽ᵉᵉ⁾
                                 (A⁽ᵉᵉ⁾ (refl A .liftr a.10)
                                      (refl A .liftr a.11)
                                  .trr a.12)
                                 (refl A .liftl (refl A .trr a.11))
                             .liftl (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))))
                         (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .trl.1 (refl a.01))
                              (A⁽ᵉᵉ⁾
                                   (A⁽ᵉᵉ⁾ (refl A .liftr a.10)
                                        (refl A .liftr a.11)
                                    .trr a.12)
                                   (refl A .liftl (refl A .trr a.11))
                               .trl (A⁽ᵉᵉ⁾ .trr.1 (refl a.11)))
                          .liftr
                            (A⁽ᵉᵉ⁾
                                 (A⁽ᵉᵉ⁾ a.02 (refl A .liftl a.01)
                                  .trl (refl a.01)) (refl A .liftr a.10)
                             .trr a.20))
                         (A⁽ᵉᵉ⁾ (refl a.01) (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))
                          .liftr
                            (A⁽ᵉᵉ⁾ (refl a.01) (refl A .liftr a.11) .trr a.21))
                     .trr
                       (A⁽ᵉᵉᵉ⁾
                            (sym
                               (A⁽ᵉᵉ⁾ a.02 (refl A .liftl a.01)
                                .liftl (refl a.01)))
                            (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11)
                             .liftr a.12)
                            (A⁽ᵉᵉ⁾
                                 (A⁽ᵉᵉ⁾ a.02 (refl A .liftl a.01)
                                  .trl (refl a.01)) (refl A .liftr a.10)
                             .liftr a.20)
                            (A⁽ᵉᵉ⁾ (refl a.01) (refl A .liftr a.11)
                             .liftr a.21)
                        .trr a.22))
                    (A⁽ᵉᵉ⁾ (refl A .liftl a.01)
                         (refl A .liftl (refl A .trr a.11))
                     .liftl
                       (A⁽ᵉᵉ⁾ (refl a.01) (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))
                        .trr
                          (A⁽ᵉᵉ⁾ (refl a.01) (refl A .liftr a.11) .trr a.21)))
                .trl
                  (A⁽ᵉᵉᵉ⁾ a.01⁽ᵉᵉ⁾ (A⁽ᵉᵉᵉ⁾ .trr.1 a.11⁽ᵉᵉ⁾)
                   .trr.1
                     (A⁽ᵉᵉᵉ⁾ a.01⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.11))
                      .trr.1 (refl a.21)))))
            (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01)))
                 (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))))
             .trr.1
               (f⁽ᵉᵉ⁾
                  (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftl.1 (refl a.01))
                       (A⁽ᵉᵉ⁾ .liftl.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.11)))
                   .trl.1
                     (A⁽ᵉᵉᵉ⁾ a.01⁽ᵉᵉ⁾ (A⁽ᵉᵉᵉ⁾ .trr.1 a.11⁽ᵉᵉ⁾)
                      .trr.1
                        (A⁽ᵉᵉᵉ⁾ a.01⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.11))
                         .trr.1 (refl a.21))))))
        .trl
          (B⁽ᵉᵉ⁾ (refl f (refl A .liftl a.01))
               (refl f (refl A .liftl (refl A .trr a.11)))
           .liftr
             (refl f
                (A⁽ᵉᵉ⁾ (refl A .liftl a.01)
                     (refl A .liftl (refl A .trr a.11))
                 .trl
                   (A⁽ᵉᵉ⁾ (refl a.01) (A⁽ᵉᵉ⁾ .trr.1 (refl a.11))
                    .trr (A⁽ᵉᵉ⁾ (refl a.01) (refl A .liftr a.11) .trr a.21)))))))
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀)
              (B⁽ᵉᵉ⁾ (refl f (refl A .liftl 𝑥₀₁))
                   (refl f (refl A .liftl 𝑥₁₁))
               .trr
                 (refl f
                    (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₁) (refl A .liftl 𝑥₁₁) .trl 𝑥₂₁)))
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .trl
    : ({𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁))
      → {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁)
  
  a ⤇
  B⁽ᵉᵉ⁾ (refl f (refl A .liftr a.0)) (refl f (refl A .liftr a.1))
  .trl (refl f (A⁽ᵉᵉ⁾ (refl A .liftr a.0) (refl A .liftr a.1) .trr a.2))
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁)
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .liftl
    : (x₁ : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (f 𝑥₀) (f 𝑥₁))
      → {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
        {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
        (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂)
                (B⁽ᵉᵉ⁾ (refl f (refl A .liftr 𝑥₀₀))
                     (refl f (refl A .liftr 𝑥₁₀))
                 .trl
                   (x₁
                      (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₀) (refl A .liftr 𝑥₁₀) .trr 𝑥₂₀)))
                (x₁ 𝑥₂₁)
  
  a ⤇
  B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (sym (A⁽ᵉᵉ⁾ a.02 (refl A .liftr a.00) .liftr (refl a.00))))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11) .liftr a.12))
      (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00)))
           (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl A .liftr a.10)))
       .trl.1
         (f⁽ᵉᵉ⁾
            (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00))
                 (A⁽ᵉᵉ⁾ .liftr.1 (refl A .liftr a.10))
             .trr.1 (A⁽ᵉᵉ⁾ (refl a.00) (refl A .liftr a.10) .liftr a.20))))
      (f⁽ᵉᵉ⁾
         (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ a.02 (refl A .liftr a.00) .trr (refl a.00))
              (refl A .liftr a.11)
          .liftr a.21))
  .trl
    (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00)))
         (f⁽ᵉᵉ⁾
            (sym
               (A⁽ᵉᵉ⁾
                    (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11)
                     .trr a.12) (refl A .liftr (refl A .trr a.10))
                .liftr (A⁽ᵉᵉ⁾ .trr.1 (refl a.10)))))
         (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00)))
              (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))))
          .trl.1
            (f⁽ᵉᵉ⁾
               (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00))
                    (A⁽ᵉᵉ⁾ .liftr.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.10)))
                .trr.1
                  (A⁽ᵉᵉ⁾ (refl a.00) (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))
                   .liftr (A⁽ᵉᵉ⁾ (refl a.00) (refl A .liftr a.10) .trr a.20)))))
         (f⁽ᵉᵉ⁾
            (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .trr.1 (refl a.00))
                 (A⁽ᵉᵉ⁾
                      (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11)
                       .trr a.12) (refl A .liftr (refl A .trr a.10))
                  .trr (A⁽ᵉᵉ⁾ .trr.1 (refl a.10)))
             .liftr
               (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ a.02 (refl A .liftr a.00) .trr (refl a.00))
                    (refl A .liftr a.11)
                .trr a.21)))
     .trl
       (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00)))
            (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))))
            (B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00)))
                 (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))))
             .trl.1
               (f⁽ᵉᵉ⁾
                  (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00))
                       (A⁽ᵉᵉ⁾ .liftr.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.10)))
                   .trr.1
                     (A⁽ᵉᵉᵉ⁾ a.00⁽ᵉᵉ⁾ (A⁽ᵉᵉᵉ⁾ .trr.1 a.10⁽ᵉᵉ⁾)
                      .trr.1
                        (A⁽ᵉᵉᵉ⁾ a.00⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.10))
                         .trr.1 (refl a.20))))))
            (f⁽ᵉᵉ⁾
               (A⁽ᵉᵉᵉ⁾ (sym (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00)))
                    (sym (A⁽ᵉᵉ⁾ .liftr.1 (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))))
                    (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.00))
                         (sym
                            (A⁽ᵉᵉ⁾
                                 (A⁽ᵉᵉ⁾ (refl A .liftr a.10)
                                      (refl A .liftr a.11)
                                  .trr a.12)
                                 (refl A .liftr (refl A .trr a.10))
                             .liftr (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))))
                         (A⁽ᵉᵉ⁾ (refl a.00) (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))
                          .liftr
                            (A⁽ᵉᵉ⁾ (refl a.00) (refl A .liftr a.10) .trr a.20))
                         (A⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .trr.1 (refl a.00))
                              (A⁽ᵉᵉ⁾
                                   (A⁽ᵉᵉ⁾ (refl A .liftr a.10)
                                        (refl A .liftr a.11)
                                    .trr a.12)
                                   (refl A .liftr (refl A .trr a.10))
                               .trr (A⁽ᵉᵉ⁾ .trr.1 (refl a.10)))
                          .liftr
                            (A⁽ᵉᵉ⁾
                                 (A⁽ᵉᵉ⁾ a.02 (refl A .liftr a.00)
                                  .trr (refl a.00)) (refl A .liftr a.11)
                             .trr a.21))
                     .trr
                       (A⁽ᵉᵉᵉ⁾
                            (sym
                               (A⁽ᵉᵉ⁾ a.02 (refl A .liftr a.00)
                                .liftr (refl a.00)))
                            (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11)
                             .liftr a.12)
                            (A⁽ᵉᵉ⁾ (refl a.00) (refl A .liftr a.10)
                             .liftr a.20)
                            (A⁽ᵉᵉ⁾
                                 (A⁽ᵉᵉ⁾ a.02 (refl A .liftr a.00)
                                  .trr (refl a.00)) (refl A .liftr a.11)
                             .liftr a.21)
                        .trr a.22))
                    (A⁽ᵉᵉ⁾ (refl A .liftr a.00)
                         (refl A .liftr (refl A .trr a.10))
                     .liftr
                       (A⁽ᵉᵉ⁾ (refl a.00) (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))
                        .trr
                          (A⁽ᵉᵉ⁾ (refl a.00) (refl A .liftr a.10) .trr a.20)))
                .trr
                  (A⁽ᵉᵉᵉ⁾ a.00⁽ᵉᵉ⁾ (A⁽ᵉᵉᵉ⁾ .trr.1 a.10⁽ᵉᵉ⁾)
                   .trr.1
                     (A⁽ᵉᵉᵉ⁾ a.00⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ .liftr.1 (refl a.10))
                      .trr.1 (refl a.20)))))
        .trl
          (B⁽ᵉᵉ⁾ (refl f (refl A .liftr a.00))
               (refl f (refl A .liftr (refl A .trr a.10)))
           .liftl
             (refl f
                (A⁽ᵉᵉ⁾ (refl A .liftr a.00)
                     (refl A .liftr (refl A .trr a.10))
                 .trr
                   (A⁽ᵉᵉ⁾ (refl a.00) (A⁽ᵉᵉ⁾ .trr.1 (refl a.10))
                    .trr (A⁽ᵉᵉ⁾ (refl a.00) (refl A .liftr a.10) .trr a.20)))))))
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂)
              (B⁽ᵉᵉ⁾ (refl f (refl A .liftr 𝑥₀₀))
                   (refl f (refl A .liftr 𝑥₁₀))
               .trl
                 (refl f
                    (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₀) (refl A .liftr 𝑥₁₀) .trr 𝑥₂₀)))
              (refl f 𝑥₂₁)
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .trr
    : ({𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
       {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
       (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
       →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁))
      → {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
        {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
        (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁)
  
  a ⤇
  B⁽ᵉᵉᵉ⁾
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftl a.00) (refl A .liftl a.01) .liftl a.02))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftl a.10) (refl A .liftl a.11) .liftl a.12))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftl a.00) (refl A .liftl a.10) .liftl a.20))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftl a.01) (refl A .liftl a.11) .liftl a.21))
  .trr
    (f⁽ᵉᵉ⁾
       (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftl a.00) (refl A .liftl a.01) .liftl a.02)
            (A⁽ᵉᵉ⁾ (refl A .liftl a.10) (refl A .liftl a.11) .liftl a.12)
            (A⁽ᵉᵉ⁾ (refl A .liftl a.00) (refl A .liftl a.10) .liftl a.20)
            (A⁽ᵉᵉ⁾ (refl A .liftl a.01) (refl A .liftl a.11) .liftl a.21)
        .trl a.22))
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁)
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .liftr
    : (x₀
      : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
        {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
        (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁))
      → {𝑥₀₀₀ : A} {𝑥₀₀₁ : A} {𝑥₀₀₂ : Id A 𝑥₀₀₀ 𝑥₀₀₁} {𝑥₀₁₀ : A} {𝑥₀₁₁ : A}
        {𝑥₀₁₂ : Id A 𝑥₀₁₀ 𝑥₀₁₁} {𝑥₀₂₀ : Id A 𝑥₀₀₀ 𝑥₀₁₀}
        {𝑥₀₂₁ : Id A 𝑥₀₀₁ 𝑥₀₁₁} {𝑥₀₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₀₂ 𝑥₀₁₂ 𝑥₀₂₀ 𝑥₀₂₁} {𝑥₁₀₀ : A}
        {𝑥₁₀₁ : A} {𝑥₁₀₂ : Id A 𝑥₁₀₀ 𝑥₁₀₁} {𝑥₁₁₀ : A} {𝑥₁₁₁ : A}
        {𝑥₁₁₂ : Id A 𝑥₁₁₀ 𝑥₁₁₁} {𝑥₁₂₀ : Id A 𝑥₁₀₀ 𝑥₁₁₀}
        {𝑥₁₂₁ : Id A 𝑥₁₀₁ 𝑥₁₁₁} {𝑥₁₂₂ : A⁽ᵉᵉ⁾ 𝑥₁₀₂ 𝑥₁₁₂ 𝑥₁₂₀ 𝑥₁₂₁}
        {𝑥₂₀₀ : Id A 𝑥₀₀₀ 𝑥₁₀₀} {𝑥₂₀₁ : Id A 𝑥₀₀₁ 𝑥₁₀₁}
        {𝑥₂₀₂ : A⁽ᵉᵉ⁾ 𝑥₀₀₂ 𝑥₁₀₂ 𝑥₂₀₀ 𝑥₂₀₁} {𝑥₂₁₀ : Id A 𝑥₀₁₀ 𝑥₁₁₀}
        {𝑥₂₁₁ : Id A 𝑥₀₁₁ 𝑥₁₁₁} {𝑥₂₁₂ : A⁽ᵉᵉ⁾ 𝑥₀₁₂ 𝑥₁₁₂ 𝑥₂₁₀ 𝑥₂₁₁}
        {𝑥₂₂₀ : A⁽ᵉᵉ⁾ 𝑥₀₂₀ 𝑥₁₂₀ 𝑥₂₀₀ 𝑥₂₁₀} {𝑥₂₂₁ : A⁽ᵉᵉ⁾ 𝑥₀₂₁ 𝑥₁₂₁ 𝑥₂₀₁ 𝑥₂₁₁}
        (𝑥₂₂₂ : A⁽ᵉᵉᵉ⁾ 𝑥₀₂₂ 𝑥₁₂₂ 𝑥₂₀₂ 𝑥₂₁₂ 𝑥₂₂₀ 𝑥₂₂₁)
        →⁽ᵉᵉᵉ⁾ B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ 𝑥₀₂₂) (f⁽ᵉᵉ⁾ 𝑥₁₂₂) (f⁽ᵉᵉ⁾ 𝑥₂₀₂) (f⁽ᵉᵉ⁾ 𝑥₂₁₂)
                 (x₀ 𝑥₂₂₀)
                 (B⁽ᵉᵉᵉ⁾
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₀₁) (refl A .liftl 𝑥₀₁₁)
                          .liftl 𝑥₀₂₁))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₁₀₁) (refl A .liftl 𝑥₁₁₁)
                          .liftl 𝑥₁₂₁))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₀₁) (refl A .liftl 𝑥₁₀₁)
                          .liftl 𝑥₂₀₁))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₁₁) (refl A .liftl 𝑥₁₁₁)
                          .liftl 𝑥₂₁₁))
                  .trr
                    (x₀
                       (A⁽ᵉᵉᵉ⁾
                            (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₀₁) (refl A .liftl 𝑥₀₁₁)
                             .liftl 𝑥₀₂₁)
                            (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₁₀₁) (refl A .liftl 𝑥₁₁₁)
                             .liftl 𝑥₁₂₁)
                            (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₀₁) (refl A .liftl 𝑥₁₀₁)
                             .liftl 𝑥₂₀₁)
                            (A⁽ᵉᵉ⁾ (refl A .liftl 𝑥₀₁₁) (refl A .liftl 𝑥₁₁₁)
                             .liftl 𝑥₂₁₁)
                        .trl 𝑥₂₂₁)))
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .trl
    : ({𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
       {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
       (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
       →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁))
      → {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
        {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
        (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁)
  
  a ⤇
  B⁽ᵉᵉᵉ⁾
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftr a.00) (refl A .liftr a.01) .liftr a.02))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11) .liftr a.12))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftr a.00) (refl A .liftr a.10) .liftr a.20))
      (f⁽ᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftr a.01) (refl A .liftr a.11) .liftr a.21))
  .trl
    (f⁽ᵉᵉ⁾
       (A⁽ᵉᵉᵉ⁾ (A⁽ᵉᵉ⁾ (refl A .liftr a.00) (refl A .liftr a.01) .liftr a.02)
            (A⁽ᵉᵉ⁾ (refl A .liftr a.10) (refl A .liftr a.11) .liftr a.12)
            (A⁽ᵉᵉ⁾ (refl A .liftr a.00) (refl A .liftr a.10) .liftr a.20)
            (A⁽ᵉᵉ⁾ (refl A .liftr a.01) (refl A .liftr a.11) .liftr a.21)
        .trr a.22))
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁)
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .liftl
    : (x₁
      : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
        {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
        (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f 𝑥₀₂) (refl f 𝑥₁₂) (refl f 𝑥₂₀) (refl f 𝑥₂₁))
      → {𝑥₀₀₀ : A} {𝑥₀₀₁ : A} {𝑥₀₀₂ : Id A 𝑥₀₀₀ 𝑥₀₀₁} {𝑥₀₁₀ : A} {𝑥₀₁₁ : A}
        {𝑥₀₁₂ : Id A 𝑥₀₁₀ 𝑥₀₁₁} {𝑥₀₂₀ : Id A 𝑥₀₀₀ 𝑥₀₁₀}
        {𝑥₀₂₁ : Id A 𝑥₀₀₁ 𝑥₀₁₁} {𝑥₀₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₀₂ 𝑥₀₁₂ 𝑥₀₂₀ 𝑥₀₂₁} {𝑥₁₀₀ : A}
        {𝑥₁₀₁ : A} {𝑥₁₀₂ : Id A 𝑥₁₀₀ 𝑥₁₀₁} {𝑥₁₁₀ : A} {𝑥₁₁₁ : A}
        {𝑥₁₁₂ : Id A 𝑥₁₁₀ 𝑥₁₁₁} {𝑥₁₂₀ : Id A 𝑥₁₀₀ 𝑥₁₁₀}
        {𝑥₁₂₁ : Id A 𝑥₁₀₁ 𝑥₁₁₁} {𝑥₁₂₂ : A⁽ᵉᵉ⁾ 𝑥₁₀₂ 𝑥₁₁₂ 𝑥₁₂₀ 𝑥₁₂₁}
        {𝑥₂₀₀ : Id A 𝑥₀₀₀ 𝑥₁₀₀} {𝑥₂₀₁ : Id A 𝑥₀₀₁ 𝑥₁₀₁}
        {𝑥₂₀₂ : A⁽ᵉᵉ⁾ 𝑥₀₀₂ 𝑥₁₀₂ 𝑥₂₀₀ 𝑥₂₀₁} {𝑥₂₁₀ : Id A 𝑥₀₁₀ 𝑥₁₁₀}
        {𝑥₂₁₁ : Id A 𝑥₀₁₁ 𝑥₁₁₁} {𝑥₂₁₂ : A⁽ᵉᵉ⁾ 𝑥₀₁₂ 𝑥₁₁₂ 𝑥₂₁₀ 𝑥₂₁₁}
        {𝑥₂₂₀ : A⁽ᵉᵉ⁾ 𝑥₀₂₀ 𝑥₁₂₀ 𝑥₂₀₀ 𝑥₂₁₀} {𝑥₂₂₁ : A⁽ᵉᵉ⁾ 𝑥₀₂₁ 𝑥₁₂₁ 𝑥₂₀₁ 𝑥₂₁₁}
        (𝑥₂₂₂ : A⁽ᵉᵉᵉ⁾ 𝑥₀₂₂ 𝑥₁₂₂ 𝑥₂₀₂ 𝑥₂₁₂ 𝑥₂₂₀ 𝑥₂₂₁)
        →⁽ᵉᵉᵉ⁾ B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ 𝑥₀₂₂) (f⁽ᵉᵉ⁾ 𝑥₁₂₂) (f⁽ᵉᵉ⁾ 𝑥₂₀₂) (f⁽ᵉᵉ⁾ 𝑥₂₁₂)
                 (B⁽ᵉᵉᵉ⁾
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₀₀) (refl A .liftr 𝑥₀₁₀)
                          .liftr 𝑥₀₂₀))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₁₀₀) (refl A .liftr 𝑥₁₁₀)
                          .liftr 𝑥₁₂₀))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₀₀) (refl A .liftr 𝑥₁₀₀)
                          .liftr 𝑥₂₀₀))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₁₀) (refl A .liftr 𝑥₁₁₀)
                          .liftr 𝑥₂₁₀))
                  .trl
                    (x₁
                       (A⁽ᵉᵉᵉ⁾
                            (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₀₀) (refl A .liftr 𝑥₀₁₀)
                             .liftr 𝑥₀₂₀)
                            (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₁₀₀) (refl A .liftr 𝑥₁₁₀)
                             .liftr 𝑥₁₂₀)
                            (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₀₀) (refl A .liftr 𝑥₁₀₀)
                             .liftr 𝑥₂₀₀)
                            (A⁽ᵉᵉ⁾ (refl A .liftr 𝑥₀₁₀) (refl A .liftr 𝑥₁₁₀)
                             .liftr 𝑥₂₁₀)
                        .trr 𝑥₂₂₀))) (x₁ 𝑥₂₂₁)
  
  a ⤇
  B⁽ᵉᵉᵉᵉ⁾
      (f⁽ᵉᵉᵉ⁾
         (A⁽ᵉᵉᵉ⁾
              (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.001) .liftl a.002)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.011) .liftl a.012)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.010) .liftl a.020)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.011) .liftl a.021)
          .liftl a.022))
      (f⁽ᵉᵉᵉ⁾
         (A⁽ᵉᵉᵉ⁾
              (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.101) .liftl a.102)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.110) (refl A .liftl a.111) .liftl a.112)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.110) .liftl a.120)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.101) (refl A .liftl a.111) .liftl a.121)
          .liftl a.122))
      (f⁽ᵉᵉᵉ⁾
         (A⁽ᵉᵉᵉ⁾
              (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.001) .liftl a.002)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.101) .liftl a.102)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.100) .liftl a.200)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.101) .liftl a.201)
          .liftl a.202))
      (f⁽ᵉᵉᵉ⁾
         (A⁽ᵉᵉᵉ⁾
              (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.011) .liftl a.012)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.110) (refl A .liftl a.111) .liftl a.112)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.110) .liftl a.210)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.011) (refl A .liftl a.111) .liftl a.211)
          .liftl a.212))
      (f⁽ᵉᵉᵉ⁾
         (A⁽ᵉᵉᵉ⁾
              (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.010) .liftl a.020)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.110) .liftl a.120)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.100) .liftl a.200)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.110) .liftl a.210)
          .liftl a.220))
      (f⁽ᵉᵉᵉ⁾
         (A⁽ᵉᵉᵉ⁾
              (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.011) .liftl a.021)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.101) (refl A .liftl a.111) .liftl a.121)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.101) .liftl a.201)
              (A⁽ᵉᵉ⁾ (refl A .liftl a.011) (refl A .liftl a.111) .liftl a.211)
          .liftl a.221))
  .trr
    (f⁽ᵉᵉᵉ⁾
       (A⁽ᵉᵉᵉᵉ⁾
            (A⁽ᵉᵉᵉ⁾
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.001)
                  .liftl a.002)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.011)
                  .liftl a.012)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.010)
                  .liftl a.020)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.011)
                  .liftl a.021)
             .liftl a.022)
            (A⁽ᵉᵉᵉ⁾
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.101)
                  .liftl a.102)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.110) (refl A .liftl a.111)
                  .liftl a.112)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.110)
                  .liftl a.120)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.101) (refl A .liftl a.111)
                  .liftl a.121)
             .liftl a.122)
            (A⁽ᵉᵉᵉ⁾
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.001)
                  .liftl a.002)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.101)
                  .liftl a.102)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.100)
                  .liftl a.200)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.101)
                  .liftl a.201)
             .liftl a.202)
            (A⁽ᵉᵉᵉ⁾
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.011)
                  .liftl a.012)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.110) (refl A .liftl a.111)
                  .liftl a.112)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.110)
                  .liftl a.210)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.011) (refl A .liftl a.111)
                  .liftl a.211)
             .liftl a.212)
            (A⁽ᵉᵉᵉ⁾
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.010)
                  .liftl a.020)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.100) (refl A .liftl a.110)
                  .liftl a.120)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.000) (refl A .liftl a.100)
                  .liftl a.200)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.010) (refl A .liftl a.110)
                  .liftl a.210)
             .liftl a.220)
            (A⁽ᵉᵉᵉ⁾
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.011)
                  .liftl a.021)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.101) (refl A .liftl a.111)
                  .liftl a.121)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.001) (refl A .liftl a.101)
                  .liftl a.201)
                 (A⁽ᵉᵉ⁾ (refl A .liftl a.011) (refl A .liftl a.111)
                  .liftl a.211)
             .liftl a.221)
        .trl a.222))
    : {𝑥₀₀₀ : A} {𝑥₀₀₁ : A} {𝑥₀₀₂ : Id A 𝑥₀₀₀ 𝑥₀₀₁} {𝑥₀₁₀ : A} {𝑥₀₁₁ : A}
      {𝑥₀₁₂ : Id A 𝑥₀₁₀ 𝑥₀₁₁} {𝑥₀₂₀ : Id A 𝑥₀₀₀ 𝑥₀₁₀} {𝑥₀₂₁ : Id A 𝑥₀₀₁ 𝑥₀₁₁}
      {𝑥₀₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₀₂ 𝑥₀₁₂ 𝑥₀₂₀ 𝑥₀₂₁} {𝑥₁₀₀ : A} {𝑥₁₀₁ : A}
      {𝑥₁₀₂ : Id A 𝑥₁₀₀ 𝑥₁₀₁} {𝑥₁₁₀ : A} {𝑥₁₁₁ : A} {𝑥₁₁₂ : Id A 𝑥₁₁₀ 𝑥₁₁₁}
      {𝑥₁₂₀ : Id A 𝑥₁₀₀ 𝑥₁₁₀} {𝑥₁₂₁ : Id A 𝑥₁₀₁ 𝑥₁₁₁}
      {𝑥₁₂₂ : A⁽ᵉᵉ⁾ 𝑥₁₀₂ 𝑥₁₁₂ 𝑥₁₂₀ 𝑥₁₂₁} {𝑥₂₀₀ : Id A 𝑥₀₀₀ 𝑥₁₀₀}
      {𝑥₂₀₁ : Id A 𝑥₀₀₁ 𝑥₁₀₁} {𝑥₂₀₂ : A⁽ᵉᵉ⁾ 𝑥₀₀₂ 𝑥₁₀₂ 𝑥₂₀₀ 𝑥₂₀₁}
      {𝑥₂₁₀ : Id A 𝑥₀₁₀ 𝑥₁₁₀} {𝑥₂₁₁ : Id A 𝑥₀₁₁ 𝑥₁₁₁}
      {𝑥₂₁₂ : A⁽ᵉᵉ⁾ 𝑥₀₁₂ 𝑥₁₁₂ 𝑥₂₁₀ 𝑥₂₁₁} {𝑥₂₂₀ : A⁽ᵉᵉ⁾ 𝑥₀₂₀ 𝑥₁₂₀ 𝑥₂₀₀ 𝑥₂₁₀}
      {𝑥₂₂₁ : A⁽ᵉᵉ⁾ 𝑥₀₂₁ 𝑥₁₂₁ 𝑥₂₀₁ 𝑥₂₁₁}
      (𝑥₂₂₂ : A⁽ᵉᵉᵉ⁾ 𝑥₀₂₂ 𝑥₁₂₂ 𝑥₂₀₂ 𝑥₂₁₂ 𝑥₂₂₀ 𝑥₂₂₁)
      →⁽ᵉᵉᵉ⁾ B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ 𝑥₀₂₂) (f⁽ᵉᵉ⁾ 𝑥₁₂₂) (f⁽ᵉᵉ⁾ 𝑥₂₀₂) (f⁽ᵉᵉ⁾ 𝑥₂₁₂)
               (f⁽ᵉᵉ⁾ 𝑥₂₂₀) (f⁽ᵉᵉ⁾ 𝑥₂₂₁)
  

  $ narya -v match_in_type.ny
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/match_in_type.ny
   3 | def test (m : ⊤) : match m [ star. ↦ sig () ] ≔ ?
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant test defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     m : ⊤
     ----------------------------------------------------------------------
     _match.F2.0{…}
  
   ￫ error[E3002]
   ￮ file match_in_type.ny contains open holes
  
  [1]

This bug was in highlighting the whole degeneracy term rather than just its argument.

  $ narya -use-ansi check_refl_loc.ny 2>&1 | sed 's/\x1b/ESC/g'
   ￫ ESC[31merror[E0401]ESC[m
   ￭ $TESTCASE_ROOT/check_refl_loc.ny
   ESC[2m9 |ESC[m def idx : Id A x x := refl ESC[4;31myESC[m
     ESC[2m^ESC[m ESC[31mterm synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         AESC[m
  
  $ narya ascvar.ny
  b
    : B
  
