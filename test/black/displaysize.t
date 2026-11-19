A displayed term that is too large is truncated, with the omitted subterms shown as "…" and a notice.  Here T doubles the size of the normal form of its argument, so the second echo would display about a million subterms.

  $ narya - <<EOF
  > axiom A : Type
  > def T (X : Type) : Type ≔ X → X → Type
  > echo T (T A)
  > echo T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T A)))))))))))))))))))
  > display size ≔ 12
  > echo T (T A)
  > display size ≔ ∞
  > echo T (T (T A))
  > EOF
  (A → A → Type) → (A → A → Type) → Type
    : Type
  
  (((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
   ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
   → Type) →
  (((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
   ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
   → Type)
  → Type
    (truncated: larger than display size 2000)
    : Type
  
  ⋯ → ⋯ → Type
    (truncated: larger than display size 12)
    : Type
  
  ((A → A → Type) → (A → A → Type) → Type) →
  ((A → A → Type) → (A → A → Type) → Type)
  → Type
    : Type
  

The same limit applies to error messages.

  $ narya - <<EOF
  > axiom A : Type
  > def T (X : Type) : Type ≔ X → X → Type
  > def bad : T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T A))))))))))))))))))) ≔ Type
  > EOF
   ￫ error[E0401]
   ￭ stdin
   3 | def bad : T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T A))))))))))))))))))) ≔ Type
     ^ term synthesized type
         Type
       but is being checked against type
         (((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
          ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
          → Type) →
         (((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
          ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
          → Type)
         → Type
         (truncated: larger than display size 2000)
       unequal head terms:
         Type
       does not equal
         ((((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
           ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
           → Type) →
          (((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
           ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
           → Type)
          → Type) →
         ((((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
           ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
           → Type) →
          (((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type) →
           ((⋯ → ⋯ → Type) → (⋯ → ⋯ → Type) → Type)
           → Type)
          → Type)
         → Type
         (truncated: larger than display size 2000)
  
  [1]

And the display size can be set from the command line.

  $ narya -display-size 12 -e 'axiom A : Type' -e 'def T (X : Type) : Type ≔ X → X → Type' -e 'echo T (T A)'
  ⋯ → ⋯ → Type
    (truncated: larger than display size 12)
    : Type
  

The marker of an omitted subterm, in either spelling, can't be re-entered, but gives a helpful error message.  (In particular, it isn't the ellipsis "…" that inserts implicit arguments.)

  $ narya -ascii -display-size 12 -e 'axiom A : Type' -e 'def T (X : Type) : Type := X -> X -> Type' -e 'echo T (T A)'
  .... -> .... -> Type
    (truncated: larger than display size 12)
    : Type
  
  $ narya -e 'axiom A : Type' -e 'echo ⋯ → A'
   ￫ error[E0209]
   ￭ command-line exec string
   1 | echo ⋯ → A
     ^ display-only syntax can't be parsed: '⋯', which marks a part of a term omitted from display
  
  [1]
  $ narya -e 'axiom A : Type' -e 'echo .... -> A'
   ￫ error[E0209]
   ￭ command-line exec string
   1 | echo .... -> A
     ^ display-only syntax can't be parsed: '⋯', which marks a part of a term omitted from display
  
  [1]
