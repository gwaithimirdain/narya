def List : Type → Type ≔ A ↦ data [ nil. | cons. (x : A) (xs : List A) ]

axiom A : Type
axiom a : A

def id00 : Id (List A) nil. nil. ≔ nil.
def id11 : Id (List A) (cons. a nil.) (cons. a nil.) ≔ cons. (refl a) nil.
def id22 : Id (List A) (cons. a (cons. a nil.)) (cons. a (cons. a nil.))
  ≔ cons. (refl a) (cons. (refl a) nil.)

{`Check that the induction principle has the right type`}
def List_ind
  : (A : Type) (P : List A → Type) (pn : P nil.)
    (pc : (a : A) (l : List A) → P l → P (cons. a l)) (l : List A)
    → P l
  ≔ A P pn pc l ↦ match l [
| nil. ↦ pn
| cons. a l ↦ pc a l (List_ind A P pn pc l)]

def indty
  ≔ (A : Type) (P : List A → Type) (pn : P nil.)
    (pc : (a : A) (l : List A) → P l → P (cons. a l)) (l : List A)
    → P l
def indty'
  ≔ (A : Type) (C : List A → Type) → C nil. →
    ((x : A) (xs : List A) → C xs → C (cons. x xs)) → (xs : List A)
    → C xs

def indty_eq_indty' : Id Type indty indty' ≔ refl indty

{`We can define concatenation by induction`}
def concat : (A : Type) → List A → List A → List A
  ≔ A xs ys ↦ List_ind A (_ ↦ List A) ys (x _ xs_ys ↦ cons. x xs_ys) xs

axiom a0 : A
axiom a1 : A
axiom a2 : A
axiom a3 : A
axiom a4 : A
def ra01 : List A ≔ cons. a0 (cons. a1 nil.)
def ra234 : List A ≔ cons. a2 (cons. a3 (cons. a4 nil.))
def a01_234 : List A ≔ concat A ra01 ra234
def a01234 : List A
  ≔ cons. a0 (cons. a1 (cons. a2 (cons. a3 (cons. a4 nil.))))
def a01_234_eq_a01234 : Id (List A) a01_234 a01234 ≔ refl a01234

{`And prove that it is unital and associative`}
def concatlu : (A : Type) (xs : List A) → Id (List A) (concat A nil. xs) xs
  ≔ A xs ↦ refl xs

def concatru : (A : Type) (xs : List A) → Id (List A) (concat A xs nil.) xs
  ≔ A xs ↦
    List_ind A (ys ↦ Id (List A) (concat A ys nil.) ys)
      (refl (nil. : List A)) (y ys ysnil ↦ cons. (refl y) ysnil) xs

def concatassoc
  : (A : Type) (xs ys zs : List A)
    → Id (List A) (concat A (concat A xs ys) zs)
        (concat A xs (concat A ys zs))
  ≔ A xs ys zs ↦
    List_ind A
      (xs ↦
       Id (List A) (concat A (concat A xs ys) zs)
         (concat A xs (concat A ys zs))) (refl (concat A ys zs))
      (x xs IH ↦ cons. (refl x) IH) xs
