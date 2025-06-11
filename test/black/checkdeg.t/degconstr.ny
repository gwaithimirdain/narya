def Sum (A B : Type) : Type ≔ data [ left. (_ : A) | right. (_ : A) ]

axiom A : Type

axiom a : A

axiom B : Type

echo left. (refl a) : Id (Sum A B) (left. a) (left. a)

echo refl (left. a) : Id (Sum A B) (left. a) (left. a)

def List (A : Type) : Type ≔ data [ nil. | cons. : A → List A → List A ]

echo refl nil. : List A

echo refl (cons. a (cons. a nil.))
     : Id (List A) (cons. a (cons. a nil.)) (cons. a (cons. a nil.))

echo refl (refl (cons. a (cons. a nil.)))
     : Id (Id (List A)) {cons. a (cons. a nil.)} {cons. a (cons. a nil.)}
         (refl (cons. a (cons. a nil.))) {cons. a (cons. a nil.)}
         {cons. a (cons. a nil.)} (refl (cons. a (cons. a nil.)))
         (refl (cons. a (cons. a nil.))) (refl (cons. a (cons. a nil.)))
