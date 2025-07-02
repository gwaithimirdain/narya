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
  
  $ narya -hott issue84.ny
  (Id A ⇒ Id B) .trr
    : (A → B) → A → B
  
  a1 ↦ refl B .trr (f (refl A .trl a1))
    : A → B
  
  (Id A ⇒ Id B) .liftr
    : (x₀ : A → B)
      → {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁)
        →⁽ᵉ⁾ Id B (x₀ H₀) (refl B .trr (x₀ (refl A .trl H₁)))
  
  a ⤇
  B⁽ᵉᵉ⁾ (refl f (A⁽ᵉᵉ⁾ a.2 (refl A .liftl a.1) .trl (refl a.1)))
      (B⁽ᵉᵉ⁾ .trr.1 (refl f (A⁽ᵉᵉ⁾ .trl.1 (refl a.1))))
  .trl (refl B .liftr (f (refl A .trl a.1)))
    : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁)
      →⁽ᵉ⁾ Id B (f H₀) (refl B .trr (f (refl A .trl H₁)))
  
  (Id A ⇒ Id B) .trl
    : (A → B) → A → B
  
  a0 ↦ refl B .trl (f (refl A .trr a0))
    : A → B
  
  (Id A ⇒ Id B) .liftl
    : (x₁ : A → B)
      → {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁)
        →⁽ᵉ⁾ Id B (refl B .trl (x₁ (refl A .trr H₀))) (x₁ H₁)
  
  a ⤇
  B⁽ᵉᵉ⁾ (B⁽ᵉᵉ⁾ .trl.1 (refl f (A⁽ᵉᵉ⁾ .trr.1 (refl a.0))))
      (refl f (A⁽ᵉᵉ⁾ a.2 (refl A .liftr a.0) .trr (refl a.0)))
  .trl (refl B .liftl (f (refl A .trr a.0)))
    : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁)
      →⁽ᵉ⁾ Id B (refl B .trl (f (refl A .trr H₀))) (f H₁)
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .trr
    : ({H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁))
      → {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁)
  
  a ⤇
  B⁽ᵉᵉ⁾ (refl f (refl A .liftl a.0)) (refl f (refl A .liftl a.1))
  .trr (refl f (A⁽ᵉᵉ⁾ (refl A .liftl a.0) (refl A .liftl a.1) .trl a.2))
    : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁)
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .liftr
    : (x₀ : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁))
      → {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
        {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
        (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (x₀ H₂₀)
                (B⁽ᵉᵉ⁾ (refl f (refl A .liftl H₀₁))
                     (refl f (refl A .liftl H₁₁))
                 .trr
                   (x₀
                      (A⁽ᵉᵉ⁾ (refl A .liftl H₀₁) (refl A .liftl H₁₁) .trl H₂₁)))
  
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
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀)
              (B⁽ᵉᵉ⁾ (refl f (refl A .liftl H₀₁))
                   (refl f (refl A .liftl H₁₁))
               .trr
                 (refl f
                    (A⁽ᵉᵉ⁾ (refl A .liftl H₀₁) (refl A .liftl H₁₁) .trl H₂₁)))
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .trl
    : ({H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁))
      → {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁)
  
  a ⤇
  B⁽ᵉᵉ⁾ (refl f (refl A .liftr a.0)) (refl f (refl A .liftr a.1))
  .trl (refl f (A⁽ᵉᵉ⁾ (refl A .liftr a.0) (refl A .liftr a.1) .trr a.2))
    : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁)
  
  (A⁽ᵉᵉ⁾ ⇒ B⁽ᵉᵉ⁾) (ap f) (ap f) .liftl
    : (x₁ : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id B (f H₀) (f H₁))
      → {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
        {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
        (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂)
                (B⁽ᵉᵉ⁾ (refl f (refl A .liftr H₀₀))
                     (refl f (refl A .liftr H₁₀))
                 .trl
                   (x₁
                      (A⁽ᵉᵉ⁾ (refl A .liftr H₀₀) (refl A .liftr H₁₀) .trr H₂₀)))
                (x₁ H₂₁)
  
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
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂)
              (B⁽ᵉᵉ⁾ (refl f (refl A .liftr H₀₀))
                   (refl f (refl A .liftr H₁₀))
               .trl
                 (refl f
                    (A⁽ᵉᵉ⁾ (refl A .liftr H₀₀) (refl A .liftr H₁₀) .trr H₂₀)))
              (refl f H₂₁)
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .trr
    : ({H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
       {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
       (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
       →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁))
      → {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
        {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
        (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁)
  
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
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁)
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .liftr
    : (x₀
      : {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
        {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
        (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁))
      → {H₀₀₀ : A} {H₀₀₁ : A} {H₀₀₂ : Id A H₀₀₀ H₀₀₁} {H₀₁₀ : A} {H₀₁₁ : A}
        {H₀₁₂ : Id A H₀₁₀ H₀₁₁} {H₀₂₀ : Id A H₀₀₀ H₀₁₀}
        {H₀₂₁ : Id A H₀₀₁ H₀₁₁} {H₀₂₂ : A⁽ᵉᵉ⁾ H₀₀₂ H₀₁₂ H₀₂₀ H₀₂₁} {H₁₀₀ : A}
        {H₁₀₁ : A} {H₁₀₂ : Id A H₁₀₀ H₁₀₁} {H₁₁₀ : A} {H₁₁₁ : A}
        {H₁₁₂ : Id A H₁₁₀ H₁₁₁} {H₁₂₀ : Id A H₁₀₀ H₁₁₀}
        {H₁₂₁ : Id A H₁₀₁ H₁₁₁} {H₁₂₂ : A⁽ᵉᵉ⁾ H₁₀₂ H₁₁₂ H₁₂₀ H₁₂₁}
        {H₂₀₀ : Id A H₀₀₀ H₁₀₀} {H₂₀₁ : Id A H₀₀₁ H₁₀₁}
        {H₂₀₂ : A⁽ᵉᵉ⁾ H₀₀₂ H₁₀₂ H₂₀₀ H₂₀₁} {H₂₁₀ : Id A H₀₁₀ H₁₁₀}
        {H₂₁₁ : Id A H₀₁₁ H₁₁₁} {H₂₁₂ : A⁽ᵉᵉ⁾ H₀₁₂ H₁₁₂ H₂₁₀ H₂₁₁}
        {H₂₂₀ : A⁽ᵉᵉ⁾ H₀₂₀ H₁₂₀ H₂₀₀ H₂₁₀} {H₂₂₁ : A⁽ᵉᵉ⁾ H₀₂₁ H₁₂₁ H₂₀₁ H₂₁₁}
        (H₂₂₂ : A⁽ᵉᵉᵉ⁾ H₀₂₂ H₁₂₂ H₂₀₂ H₂₁₂ H₂₂₀ H₂₂₁)
        →⁽ᵉᵉᵉ⁾ B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ H₀₂₂) (f⁽ᵉᵉ⁾ H₁₂₂) (f⁽ᵉᵉ⁾ H₂₀₂) (f⁽ᵉᵉ⁾ H₂₁₂)
                 (x₀ H₂₂₀)
                 (B⁽ᵉᵉᵉ⁾
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl H₀₀₁) (refl A .liftl H₀₁₁)
                          .liftl H₀₂₁))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl H₁₀₁) (refl A .liftl H₁₁₁)
                          .liftl H₁₂₁))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl H₀₀₁) (refl A .liftl H₁₀₁)
                          .liftl H₂₀₁))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftl H₀₁₁) (refl A .liftl H₁₁₁)
                          .liftl H₂₁₁))
                  .trr
                    (x₀
                       (A⁽ᵉᵉᵉ⁾
                            (A⁽ᵉᵉ⁾ (refl A .liftl H₀₀₁) (refl A .liftl H₀₁₁)
                             .liftl H₀₂₁)
                            (A⁽ᵉᵉ⁾ (refl A .liftl H₁₀₁) (refl A .liftl H₁₁₁)
                             .liftl H₁₂₁)
                            (A⁽ᵉᵉ⁾ (refl A .liftl H₀₀₁) (refl A .liftl H₁₀₁)
                             .liftl H₂₀₁)
                            (A⁽ᵉᵉ⁾ (refl A .liftl H₀₁₁) (refl A .liftl H₁₁₁)
                             .liftl H₂₁₁)
                        .trl H₂₂₁)))
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .trl
    : ({H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
       {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
       (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
       →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁))
      → {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
        {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
        (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁)
  
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
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁)
  
  (A⁽ᵉᵉᵉ⁾ ⇒ B⁽ᵉᵉᵉ⁾) f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ f⁽ᵉᵉ⁾ .liftl
    : (x₁
      : {H₀₀ : A} {H₀₁ : A} {H₀₂ : Id A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
        {H₁₂ : Id A H₁₀ H₁₁} {H₂₀ : Id A H₀₀ H₁₀} {H₂₁ : Id A H₀₁ H₁₁}
        (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
        →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl f H₀₂) (refl f H₁₂) (refl f H₂₀) (refl f H₂₁))
      → {H₀₀₀ : A} {H₀₀₁ : A} {H₀₀₂ : Id A H₀₀₀ H₀₀₁} {H₀₁₀ : A} {H₀₁₁ : A}
        {H₀₁₂ : Id A H₀₁₀ H₀₁₁} {H₀₂₀ : Id A H₀₀₀ H₀₁₀}
        {H₀₂₁ : Id A H₀₀₁ H₀₁₁} {H₀₂₂ : A⁽ᵉᵉ⁾ H₀₀₂ H₀₁₂ H₀₂₀ H₀₂₁} {H₁₀₀ : A}
        {H₁₀₁ : A} {H₁₀₂ : Id A H₁₀₀ H₁₀₁} {H₁₁₀ : A} {H₁₁₁ : A}
        {H₁₁₂ : Id A H₁₁₀ H₁₁₁} {H₁₂₀ : Id A H₁₀₀ H₁₁₀}
        {H₁₂₁ : Id A H₁₀₁ H₁₁₁} {H₁₂₂ : A⁽ᵉᵉ⁾ H₁₀₂ H₁₁₂ H₁₂₀ H₁₂₁}
        {H₂₀₀ : Id A H₀₀₀ H₁₀₀} {H₂₀₁ : Id A H₀₀₁ H₁₀₁}
        {H₂₀₂ : A⁽ᵉᵉ⁾ H₀₀₂ H₁₀₂ H₂₀₀ H₂₀₁} {H₂₁₀ : Id A H₀₁₀ H₁₁₀}
        {H₂₁₁ : Id A H₀₁₁ H₁₁₁} {H₂₁₂ : A⁽ᵉᵉ⁾ H₀₁₂ H₁₁₂ H₂₁₀ H₂₁₁}
        {H₂₂₀ : A⁽ᵉᵉ⁾ H₀₂₀ H₁₂₀ H₂₀₀ H₂₁₀} {H₂₂₁ : A⁽ᵉᵉ⁾ H₀₂₁ H₁₂₁ H₂₀₁ H₂₁₁}
        (H₂₂₂ : A⁽ᵉᵉᵉ⁾ H₀₂₂ H₁₂₂ H₂₀₂ H₂₁₂ H₂₂₀ H₂₂₁)
        →⁽ᵉᵉᵉ⁾ B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ H₀₂₂) (f⁽ᵉᵉ⁾ H₁₂₂) (f⁽ᵉᵉ⁾ H₂₀₂) (f⁽ᵉᵉ⁾ H₂₁₂)
                 (B⁽ᵉᵉᵉ⁾
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr H₀₀₀) (refl A .liftr H₀₁₀)
                          .liftr H₀₂₀))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr H₁₀₀) (refl A .liftr H₁₁₀)
                          .liftr H₁₂₀))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr H₀₀₀) (refl A .liftr H₁₀₀)
                          .liftr H₂₀₀))
                      (f⁽ᵉᵉ⁾
                         (A⁽ᵉᵉ⁾ (refl A .liftr H₀₁₀) (refl A .liftr H₁₁₀)
                          .liftr H₂₁₀))
                  .trl
                    (x₁
                       (A⁽ᵉᵉᵉ⁾
                            (A⁽ᵉᵉ⁾ (refl A .liftr H₀₀₀) (refl A .liftr H₀₁₀)
                             .liftr H₀₂₀)
                            (A⁽ᵉᵉ⁾ (refl A .liftr H₁₀₀) (refl A .liftr H₁₁₀)
                             .liftr H₁₂₀)
                            (A⁽ᵉᵉ⁾ (refl A .liftr H₀₀₀) (refl A .liftr H₁₀₀)
                             .liftr H₂₀₀)
                            (A⁽ᵉᵉ⁾ (refl A .liftr H₀₁₀) (refl A .liftr H₁₁₀)
                             .liftr H₂₁₀)
                        .trr H₂₂₀))) (x₁ H₂₂₁)
  
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
    : {H₀₀₀ : A} {H₀₀₁ : A} {H₀₀₂ : Id A H₀₀₀ H₀₀₁} {H₀₁₀ : A} {H₀₁₁ : A}
      {H₀₁₂ : Id A H₀₁₀ H₀₁₁} {H₀₂₀ : Id A H₀₀₀ H₀₁₀} {H₀₂₁ : Id A H₀₀₁ H₀₁₁}
      {H₀₂₂ : A⁽ᵉᵉ⁾ H₀₀₂ H₀₁₂ H₀₂₀ H₀₂₁} {H₁₀₀ : A} {H₁₀₁ : A}
      {H₁₀₂ : Id A H₁₀₀ H₁₀₁} {H₁₁₀ : A} {H₁₁₁ : A} {H₁₁₂ : Id A H₁₁₀ H₁₁₁}
      {H₁₂₀ : Id A H₁₀₀ H₁₁₀} {H₁₂₁ : Id A H₁₀₁ H₁₁₁}
      {H₁₂₂ : A⁽ᵉᵉ⁾ H₁₀₂ H₁₁₂ H₁₂₀ H₁₂₁} {H₂₀₀ : Id A H₀₀₀ H₁₀₀}
      {H₂₀₁ : Id A H₀₀₁ H₁₀₁} {H₂₀₂ : A⁽ᵉᵉ⁾ H₀₀₂ H₁₀₂ H₂₀₀ H₂₀₁}
      {H₂₁₀ : Id A H₀₁₀ H₁₁₀} {H₂₁₁ : Id A H₀₁₁ H₁₁₁}
      {H₂₁₂ : A⁽ᵉᵉ⁾ H₀₁₂ H₁₁₂ H₂₁₀ H₂₁₁} {H₂₂₀ : A⁽ᵉᵉ⁾ H₀₂₀ H₁₂₀ H₂₀₀ H₂₁₀}
      {H₂₂₁ : A⁽ᵉᵉ⁾ H₀₂₁ H₁₂₁ H₂₀₁ H₂₁₁}
      (H₂₂₂ : A⁽ᵉᵉᵉ⁾ H₀₂₂ H₁₂₂ H₂₀₂ H₂₁₂ H₂₂₀ H₂₂₁)
      →⁽ᵉᵉᵉ⁾ B⁽ᵉᵉᵉ⁾ (f⁽ᵉᵉ⁾ H₀₂₂) (f⁽ᵉᵉ⁾ H₁₂₂) (f⁽ᵉᵉ⁾ H₂₀₂) (f⁽ᵉᵉ⁾ H₂₁₂)
               (f⁽ᵉᵉ⁾ H₂₂₀) (f⁽ᵉᵉ⁾ H₂₂₁)
  
