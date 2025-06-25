  $ narya -arity 0 -direction w,wk nullary.ny
  wk A
    : Type⁽ʷ⁾ .
  
  wk A
    : Type⁽ʷ⁾ .
  
  A⁽ʷʷ⁾
    : Type⁽ʷʷ⁾ . .
  
  wk a
    : wk A .
  
  a⁽ʷʷ⁾
    : A⁽ʷʷ⁾ . .
  
  a'
    : wk A .
  
  wk a'
    : A⁽ʷʷ⁾ . .
  
  a'⁽ʷ¹⁾
    : A⁽ʷʷ⁾ . .
  
  a''
    : A⁽ʷʷ⁾ . .
  
  sym a''
    : A⁽ʷʷ⁾ . .
  
  wk a''
    : A⁽ʷʷʷ⁾ . . .
  
  a''⁽ʷ¹⁾
    : A⁽ʷʷʷ⁾ . . .
  
  b
    : B .
  
  wk b
    : B⁽¹ʷ⁾ . .
  
  b⁽ʷ¹⁾
    : B⁽ʷ¹⁾ . .
  
  c
    : C . .
  
  sym c
    : sym C . .
  
  wk c
    : C⁽¹²ʷ⁾ . . .
  
  c⁽ʷ¹⁾
    : C⁽¹ʷ²⁾ . . .
  
  c⁽²¹ʷ⁾
    : C⁽²¹ʷ⁾ . . .
  
  $ narya -arity 0 -direction w,wk functions.ny
  (x : wk A) ⇒ wk B x.0
    : Type⁽ʷ⁾ .
  
  (x₀ : wk A .) →⁽ʷ⁾ wk B x₀ .
    : Type
  
  (x : A⁽ʷʷ⁾) ⇒ B⁽ʷʷ⁾ x.00
    : Type⁽ʷʷ⁾ . .
  
  ((x : A⁽ʷʷ⁾) ⇒ B⁽ʷʷ⁾ x.00) .
    : Type⁽ʷ⁾ .
  
  (x₀₀ : A⁽ʷʷ⁾ . .) →⁽ʷʷ⁾ B⁽ʷʷ⁾ x₀₀ . .
    : Type
  
  wk f
    : (x₀ : wk A .) →⁽ʷ⁾ wk B x₀ .
  
  f⁽ʷʷ⁾
    : (x₀₀ : A⁽ʷʷ⁾ . .) →⁽ʷʷ⁾ B⁽ʷʷ⁾ x₀₀ . .
  

