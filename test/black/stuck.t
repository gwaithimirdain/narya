The 'Unrealized Some' machinery that stores stuck matches must also store an outer insertion in case they are intrinsically higher-dimensional, like constants and metavariables do.

  $ narya -e 'axiom A:Type' -e 'axiom a:A' -e 'def E:Type := data[]' -e 'def f (e:E) : Id A a a := match e [ ]' -e 'axiom d:E' -e 'echo (f d)^^(e1)'
  sym (refl f (refl d))
    : A⁽ᵉᵉ⁾ (f d) (f d) (refl a) (refl a)
  
