This tests the "display unique keys" option, which controls whether unparsing
prints a key that is the unique 2-cell between its endpoints (as opposed to a
key that is an identity, which is never printed).  We work in -adjunction
mode, where the doubled counit △□△□ ⇒ 1 is such a unique nonidentity key: it
is inserted automatically (silently) whenever a △□△□-locked variable is used
where a plain one is expected.

  $ COUNIT="def counit22 (A :△□△□| Type) (x :△□△□| A) : A ≔ x"
  $ BAD="def bad (A :△□△□| Type) (x :△□△□| A) (y :△□△□| A) : Id A (counit22 A x) y ≔ refl y"

By default, the key is not displayed:

  $ narya -e "option modal ≔ adjunction $COUNIT" -e "$BAD"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def bad (A :△□△□| Type) (x :△□△□| A) (y :△□△□| A) : Id A (counit22 A x) y ≔ refl y
     ^ term synthesized type
         Id A y y
       but is being checked against type
         Id A x y
       unequal head variables:
         y
       does not equal
         x
  
  [1]


With -show-unique-keys, it is displayed explicitly:

  $ narya -show-unique-keys -e "option modal ≔ adjunction $COUNIT" -e "$BAD"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def bad (A :△□△□| Type) (x :△□△□| A) (y :△□△□| A) : Id A (counit22 A x) y ≔ refl y
     ^ term synthesized type
         Id A #ε #ε (y #ε #ε) (y #ε #ε)
       but is being checked against type
         Id A #ε #ε (x #ε #ε) (y #ε #ε)
       unequal head variables:
         y #ε #ε
       does not equal
         x #ε #ε
  
  [1]


-hide-unique-keys is the same as the default:

  $ narya -hide-unique-keys -e "option modal ≔ adjunction $COUNIT" -e "$BAD"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def bad (A :△□△□| Type) (x :△□△□| A) (y :△□△□| A) : Id A (counit22 A x) y ≔ refl y
     ^ term synthesized type
         Id A y y
       but is being checked against type
         Id A x y
       unequal head variables:
         y
       does not equal
         x
  
  [1]


The interactive "display unique keys := on" command has the same effect as
the command-line flag:

  $ narya -e "option modal ≔ adjunction display unique keys := on" -e "$COUNIT" -e "$BAD"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def bad (A :△□△□| Type) (x :△□△□| A) (y :△□△□| A) : Id A (counit22 A x) y ≔ refl y
     ^ term synthesized type
         Id A #ε #ε (y #ε #ε) (y #ε #ε)
       but is being checked against type
         Id A #ε #ε (x #ε #ε) (y #ε #ε)
       unequal head variables:
         y #ε #ε
       does not equal
         x #ε #ε
  
  [1]


Toggling it twice restores the default (hidden):

  $ narya -e "option modal ≔ adjunction display unique keys := toggle" -e "display unique keys := toggle" -e "$COUNIT" -e "$BAD"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def bad (A :△□△□| Type) (x :△□△□| A) (y :△□△□| A) : Id A (counit22 A x) y ≔ refl y
     ^ term synthesized type
         Id A y y
       but is being checked against type
         Id A x y
       unequal head variables:
         y
       does not equal
         x
  
  [1]


Identity keys are never displayed, even with -show-unique-keys: a
△□△□-locked variable used where a △□△□-locked one is expected needs no key
at all, and none is ever printed.

  $ narya -show-unique-keys -e "option modal ≔ adjunction def idkey (A :△□△□| Type) (x :△□△□| A) : A ≔ x"
