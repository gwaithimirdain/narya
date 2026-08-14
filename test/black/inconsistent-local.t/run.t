  $ narya -v inconsistency.ny
   ￫ info[I0000]
   ￮ constant ∇ defined
  
   ￫ info[I0000]
   ￮ constant Br∇ defined
  
   ￫ info[I0000]
   ￮ constant ∇′ defined
  
   ￫ info[I0000]
   ￮ constant ∇_to_∇′ defined
  
   ￫ info[I0000]
   ￮ constant ∇′_to_∇ defined
  
   ￫ info[I0000]
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant eq_of_Br∇′ defined
  
   ￫ info[I0000]
   ￮ constant 𝔹 defined
  
   ￫ info[I0000]
   ￮ constant ∅ defined
  
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ info[I0000]
   ￮ constant eqD defined
  
   ￫ info[I0000]
   ￮ constant trD defined
  
   ￫ info[I0000]
   ￮ constant true≠false defined
  
   ￫ info[I0000]
   ￮ constant ap defined
  
   ￫ info[I0000]
   ￮ constant ∇true defined
  
   ￫ info[I0000]
   ￮ constant ∇false defined
  
   ￫ info[I0000]
   ￮ constant ∇′true defined
  
   ￫ info[I0000]
   ￮ constant ∇′false defined
  
   ￫ info[I0000]
   ￮ constant ∇′true＝∇′false defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/inconsistency.ny
   53 |   : match u₀, u₁ [ nab. x₀, nab. x₁ ↦ ∇′ (eqD B x₀ x₁) ]
      ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant ∇′eqD_of_eq defined
  
   ￫ info[I0000]
   ￮ constant ∇′oops defined
  
   ￫ info[I0000]
   ￮ constant oopsD defined
  
   ￫ info[I0000]
   ￮ constant ⊘ defined
  
   ￫ info[I0000]
   ￮ constant oops defined
  
  oops
    : ⊘
  

The discrete local mode theory blocks the inconsistency.  Since a file declares its own type
theory, we check the same development under it by deriving a copy that declares that one.

  $ sed 's/inconsistent local/discrete local/' inconsistency.ny > discrete.ny

  $ narya -v discrete.ny
   ￫ error[E1706]
   ￮ modality ∇ is not tangible
  
  [1]
