{`
Narya tutorial
HoTT MURI Meeting 2025

The first 3/4 of this file is a minimal library setting up standard definitions of path algebra, and proving univalence in the form that a quasi-invertible map yields an equality of types.  You may want to skim through it looking just at the comments and the names of the main theorems, or you can skip it entirely and come back to it later when you need it.  The exercises for you start around line 420.
`}

{` Naming conventions:

1. In general, names are written in snake_case.

2. Object having one- or two-character global names should be written in a different font, like ℕ and 𝐉, but otherwise ordinary roman letters and arabic digits should be preferred.  Note that identifiers can *begin* with a digit, although they cannot consist entirely of digits.

3. Definitions and theorems primarily "about" an object X should be in a namespace X.  For instance, addition of natural numbers is ℕ.plus.  This is possible because the name of an object like ℕ can also be the prefix of a namespace.  Note that because namespaces can be patched, this principle can be adhered to even for theorems proven in a different file or library from where X was defined.  This also applies deeper, e.g. ℕ.code.prop proves that ℕ.code is a family of propositions.

4. A definition named X.⇦Y or Y.⇨X is a function from Y to X, analogous to X.of_Y or Y.to_X in OCaml conventions.  Either name is acceptable, as is simply Y⇨X, and of course the other(s) can be aliases.  (We can't use → or ⇒ since those have special meaning to Narya.)

5. A definition named X.of_Y or Y.is_X is a theorem that Y has property X.  Sometimes the "of" or "is" can be omitted, particularly if X starts with "is".

6. A definition named X.by_Y uses an assumption of Y to prove that something has property X.  For instance, contr.by_qinv transfers contractibility along a quasi-invertible map.

7. A definition named X＝Y is a theorem that X and Y are equal.  (We can't use the ordinary = character since it is an ASCII symbol, which can't appear in identifiers.)  If desired to specify the type the equality is at, we can write X＝Y_at_Z.

8. Not every theorem should be expected to fit into one of these schemes.

9. For grouping or combining within an identifier name, use the "mathematical flattened parenthesis" characters ⟮ and ⟯.  For instance, qinv.⟮of_ap⟯_⟮by_＝idfunc⟯ shows that "ap f" is quasi-invertible when "f" is equal to an identity function.
`}

{` Id-elimination (path induction) `}

def J (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (pa : P a (refl a)) (b : A) (p : Id A a b)
  : P b p
  ≔
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) p in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  refl P q (sym s) .trr.1 pa

def Jβ (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (pa : P a (refl a))
  : Id (P a (refl a)) pa (J A a P pa a (refl a))
  ≔
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) (refl a) in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  let cube ≔ refl (Id (Id A)) a⁽ᵉᵉ⁾ s a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ in
  let t ≔ cube .trr.1 a⁽ᵉᵉ⁾ in
  let c ≔ cube .liftr.1 a⁽ᵉᵉ⁾ in
  sym (P⁽ᵉᵉ⁾ (sym t) c⁽³²¹⁾) (refl pa) (refl P q (sym s) .liftr.1 pa)
    .trr.1 (refl pa)

{` Groupoid operations `}

def concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z) : Id A x z
  ≔ refl (w ↦ Id A x w) q .trr p

{` There is a built-in notation for equational reasoning:

calc x
= y
by p
= z
by q ∎

is the same as concat A x y z p q, but can also be extended to longer chains. `}

def inverse (A : Type) (x y : A) (p : Id A x y) : Id A y x
  ≔ refl (w ↦ Id A w x) p .trr (refl x)

{` Groupoid coherences `}

def p＝p1 (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) p (concat A x y y p (refl y))
  ≔ refl (Id A x y) .liftr p

def p1＝p (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x y y p (refl y)) p
  ≔ inverse (Id A x y) p (concat A x y y p (refl y)) (p＝p1 A x y p)

def p＝1p (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) p (concat A x x y (refl x) p)
  ≔ J A x (y p ↦ Id (Id A x y) p (concat A x x y (refl x) p))
      (A⁽ᵉᵉ⁾ (refl x) (refl x) .liftr (refl x)) y p

def 1p＝p (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x x y (refl x) p) p
  ≔ inverse (Id A x y) p (concat A x x y (refl x) p) (p＝1p A x y p)

def ⟮pp⟯p＝p⟮pp⟯ (A : Type) (x y z w : A) (p : Id A x y) (q : Id A y z)
  (r : Id A z w)
  : Id (Id A x w) (concat A x z w (concat A x y z p q) r)
      (concat A x y w p (concat A y z w q r))
  ≔ J A z
      (w r ↦
       Id (Id A x w) (concat A x z w (concat A x y z p q) r)
         (concat A x y w p (concat A y z w q r)))
      (calc
         (concat A x z z (concat A x y z p q) (refl z))
         = concat A x y z p q
             by p1＝p A x z (concat A x y z p q)
         = (concat A x y z p (concat A y z z q (refl z)))
             by ap (concat A x y z p) (p＝p1 A y z q) ∎) w r

def pp⁻¹＝1_sq (A : Type) (x y : A) (p : Id A x y)
  : A⁽ᵉᵉ⁾ (refl x) (inverse A x y p) p (refl x)
  ≔ J A x (y p ↦ A⁽ᵉᵉ⁾ (refl x) (inverse A x y p) p (refl x))
      (sym (A⁽ᵉᵉ⁾ (refl x) (refl x) .liftr (refl x))) y p

{` This alternative name may be easier to type. `}
def concat.assoc ≔ ⟮pp⟯p＝p⟮pp⟯

{` Connection squares `}

def conn (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A) p (refl y) p (refl y)
  ≔ J A x (y p ↦ Id (Id A) p (refl y) p (refl y)) (refl (refl x)) y p

def coconn (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A) (refl x) p (refl x) p
  ≔ J A x (y p ↦ Id (Id A) (refl x) p (refl x) p) (refl (refl x)) y p

{` Traditional function extensionality is easy to derive from the computation of Id in function-types. `}

def funext (A B : Type) (f g : A → B) (H : (x : A) → Id B (f x) (g x))
  : Id (A → B) f g
  ≔ x ⤇ calc
  f x.0
  = f x.1
      by ap f x.2
  = g x.1
      by H x.1 ∎

{` As our notion of "equivalence", we will simply use "Id Type".  However, as usual, we usually want to construct equivalences from quasi-invertible maps, so we build up some technology of those, with the goal of proving that while minimizing path algebra. `}

def qinv (A B : Type) (to : A → B) : Type ≔ sig (
  fro : B → A,
  fro_to : (a : A) → Id A (fro (to a)) a,
  to_fro : (b : B) → Id B (to (fro b)) b )

section qinv ≔

  def idfunc (A : Type) : qinv A A (x ↦ x) ≔ (
    y ↦ y,
    _ ↦ refl _,
    _ ↦ refl _)

  def compose (A B C : Type) (f : A → B) (g : B → C) (fq : qinv A B f)
    (gq : qinv B C g)
    : qinv A C (x ↦ g (f x))
    ≔ (
    fro ≔ z ↦ fq .fro (gq .fro z),
    fro_to ≔ a ↦ calc
      (fq .fro (gq .fro (g (f a))))
      = (fq .fro (f a))
          by ap (fq .fro) (gq .fro_to (f a))
      = a
          by fq .fro_to a ∎,
    to_fro ≔ c ↦ calc
      (g (f (fq .fro (gq .fro c))))
      = g (gq .fro c)
          by ap g (fq .to_fro (gq .fro c))
      = c
          by gq .to_fro c ∎)

{` Concatenating is a quasi-invertible map of identity types.  We could prove this with inverse laws, but we can also prove it with J. `}
  def of_concat (A : Type) (x y z : A) (q : Id A y z)
    : qinv (Id A x y) (Id A x z) (p ↦ concat A x y z p q)
    ≔ J A y (w r ↦ qinv (Id A x y) (Id A x w) (p ↦ concat A x y w p r))
        (refl (qinv (Id A x y) (Id A x y)) {p ↦ p}
             {p ↦ concat A x y y p (refl y)}
             (funext (Id A x y) (Id A x y) (p ↦ p)
                (p ↦ concat A x y y p (refl y)) (p ↦ p＝p1 A x y p))
         .trr (idfunc (Id A x y))) z q

{` Quasi-invertible maps are "injective". `}
  def injective (A B : Type) (e : A → B) (eq : qinv A B e) (x y : A)
    (p : Id B (e x) (e y))
    : Id A x y
    ≔ calc
    x
    = eq .fro (e x)
        by eq .fro_to x
    = eq .fro (e y)
        by ap (eq .fro) p
    = y
        by eq .fro_to y ∎

{` Using this, we can derive part of the "6 for 2" property. `}
  def 6_for_2_a (A B C D : Type) (f : A → B) (g : B → C) (h : C → D)
    (gfq : qinv A C (x ↦ g (f x))) (hgq : qinv B D (y ↦ h (g y)))
    : qinv A B f
    ≔ (
    fro ≔ y ↦ gfq .fro (g y),
    fro_to ≔ gfq .fro_to,
    to_fro ≔ y ↦
      injective B D (y ↦ h (g y)) hgq (f (gfq .fro (g y))) y
        (ap h (gfq .to_fro (g y))))

{` Our goal is now to show that if f is quasi-invertible, so is "ap f".  Intuitively, its inverse is "ap f⁻¹", but to actually make that land in the correct type requires composing with homotopies, and some nasty path algebra (see 2.11.1 in the HoTT Book).  Instead, we use the 2-out-of-6 property for the three functions

(x=y) --ap f--> (fx=fy) --ap f⁻¹--> (f⁻¹fx=f⁻¹fy) --ap f--> (ff⁻¹fx=ff⁻¹fy)

Here the pairwise composites are easily shown to be quasi-invertible, because the composites f∘f⁻¹ and f⁻¹∘f are equal to identity functions, and "ap idfunc" is clearly quasi-invertible. `}
  def ⟮of_ap⟯_⟮by_＝idfunc⟯ (A : Type) (f : A → A)
    (fe : Id (A → A) f (x ↦ x)) (x y : A)
    : qinv (Id A x y) (Id A (f x) (f y)) (p ↦ ap f p)
    ≔ ap (g ↦ qinv (Id A x y) (Id A (g x) (g y)) (p ↦ ap g p)) fe
        .trl (idfunc (Id A x y))

{` Now we can derive the general case. `}
  def of_ap (A B : Type) (f : A → B) (fq : qinv A B f) (x y : A)
    : qinv (Id A x y) (Id B (f x) (f y)) (p ↦ ap f p)
    ≔ 6_for_2_a (Id A x y) (Id B (f x) (f y))
        (Id A (fq .fro (f x)) (fq .fro (f y)))
        (Id B (f (fq .fro (f x))) (f (fq .fro (f y)))) (p ↦ ap f p)
        (q ↦ ap (fq .fro) q) (r ↦ ap f r)
        (⟮of_ap⟯_⟮by_＝idfunc⟯ A (x ↦ fq .fro (f x))
           (funext A A (x ↦ fq .fro (f x)) (x ↦ x) (fq .fro_to)) x y)
        (⟮of_ap⟯_⟮by_＝idfunc⟯ B (y ↦ f (fq .fro y))
           (funext B B (y ↦ f (fq .fro y)) (y ↦ y) (fq .to_fro)) (f x)
           (f y))

{` Combining of_ap and of_concat, we can show that a quasi-invertible map induces quasi-invertible "adjunction" maps from x=f⁻¹y to fx=y.  `}
  def adjunct (A B : Type) (f : A → B) (fq : qinv A B f) (x : A) (y : B)
    (p : Id A x (fq .fro y))
    : Id B (f x) y
    ≔ concat B (f x) (f (fq .fro y)) y (ap f p) (fq .to_fro y)

  def of_adjunct (A B : Type) (f : A → B) (fq : qinv A B f) (x : A) (y : B)
    : qinv (Id A x (fq .fro y)) (Id B (f x) y) (adjunct A B f fq x y)
    ≔ compose (Id A x (fq .fro y)) (Id B (f x) (f (fq .fro y)))
        (Id B (f x) y) (p ↦ ap f p)
        (p ↦ concat B (f x) (f (fq .fro y)) y p (fq .to_fro y))
        (of_ap A B f fq x (fq .fro y))
        (of_concat B (f x) (f (fq .fro y)) y (fq .to_fro y))

end

{` Σ-types `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

section Σ ≔

  def functor_fiber (A : Type) (B C : A → Type) (f : (x : A) → B x → C x)
    : Σ A B → Σ A C
    ≔ u ↦ (u .fst, f (u .fst) (u .snd))

  def qinv_⟮functor_fiber⟯ (A : Type) (B C : A → Type)
    (f : (x : A) → B x → C x) (fq : (x : A) → qinv (B x) (C x) (f x))
    : qinv (Σ A B) (Σ A C) (functor_fiber A B C f)
    ≔ (
    fro ≔ functor_fiber A C B (x ↦ fq x .fro),
    fro_to ≔ u ↦ (fst ≔ refl _, snd ≔ fq (u .fst) .fro_to (u .snd)),
    to_fro ≔ u ↦ (fst ≔ refl _, snd ≔ fq (u .fst) .to_fro (u .snd)))

end

{` Contractible types `}

def is_contr (A : Type) : Type ≔ sig (
  center : A,
  contract : (a : A) → Id A a center )

section is_contr ≔

  def id_to (A : Type) (a1 : A) : is_contr (Σ A (a0 ↦ Id A a0 a1)) ≔ (
    center ≔ (a1, refl a1),
    contract ≔ a0_a2 ↦
      let a0 ≔ a0_a2 .fst in
      let a2 ≔ a0_a2 .snd in
      (a2, conn A a0 a1 a2))

  def id_from (A : Type) (a0 : A) : is_contr (Σ A (a1 ↦ Id A a0 a1)) ≔ (
    center ≔ (a0, refl a0),
    contract ≔ a1_a2 ↦
      let a1 ≔ a1_a2 .fst in
      let a2 ≔ a1_a2 .snd in
      (inverse A a0 a1 a2, pp⁻¹＝1_sq A a0 a1 a2))

  def by_qinv (A B : Type) (cA : is_contr A) (e : A → B) (eq : qinv A B e)
    : is_contr B
    ≔ (
    center ≔ e (cA .center),
    contract ≔ b ↦ calc
      b
      = e (eq .fro b)
          by eq .to_fro b
      = e (cA .center)
          by refl e (cA .contract (eq .fro b)) ∎)

end

{` Quasi-invertible maps have contractible fibers.  This contains the main result of "adjointification". `}
def qinv.is_contr_fiber (A B : Type) (f : A → B) (fq : qinv A B f) (b : B)
  : is_contr (Σ A (a ↦ Id B (f a) b))
  ≔ is_contr.by_qinv (Σ A (a ↦ Id A a (fq .fro b)))
      (Σ A (a ↦ Id B (f a) b)) (is_contr.id_to A (fq .fro b))
      (Σ.functor_fiber A (a ↦ Id A a (fq .fro b)) (a ↦ Id B (f a) b)
         (a ↦ qinv.adjunct A B f fq a b))
      (Σ.qinv_⟮functor_fiber⟯ A (a ↦ Id A a (fq .fro b)) (a ↦ Id B (f a) b)
         (a ↦ qinv.adjunct A B f fq a b) (a ↦ qinv.of_adjunct A B f fq a b))

{` A 1-1 correspondence is one that's functional in both directions. `}
def is11 (A B : Type) (R : A → B → Type) : Type ≔ sig (
  contrr : (a : A) → is_contr (Σ B (R a)),
  contrl : (b : B) → is_contr (Σ A (a ↦ R a b)) )

section is11 ≔

{` A 1-1 correspondence induces another one on identity types.  This is where the real work of univalence lies. `}
  def of_Id (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 B1 : Type)
    (B2 : Id Type B0 B1) (R0 : A0 → B0 → Type) (re0 : is11 A0 B0 R0)
    (R1 : A1 → B1 → Type) (re1 : is11 A1 B1 R1)
    (R2 : Id ((X Y ↦ (X → Y → Type)) : (X Y : Type) → Type) A2 B2 R0 R1)
    (re2 : refl is11 A2 B2 R2 re0 re1) (a0 : A0) (a1 : A1) (b0 : B0)
    (b1 : B1) (r0 : R0 a0 b0) (r1 : R1 a1 b1)
    : is11 (A2 a0 a1) (B2 b0 b1) (a2 b2 ↦ R2 a2 b2 r0 r1)
    ≔ (
    contrr ≔ a2 ↦
      let S : (y0 : B0) (y1 : B1) → R0 a0 y0 → R1 a1 y1 → Type
        ≔ y0 y1 z0 z1 ↦ Σ (B2 y0 y1) (y2 ↦ R2 a2 y2 z0 z1) in
      let b0' : B0 ≔ re0 .contrr a0 .center .fst in
      let b1' : B1 ≔ re1 .contrr a1 .center .fst in
      let r0' : R0 a0 b0' ≔ re0 .contrr a0 .center .snd in
      let r1' : R1 a1 b1' ≔ re1 .contrr a1 .center .snd in
      let u : S b0' b1' r0' r1' ≔ (
        re2 .contrr a2 .center .fst,
        re2 .contrr a2 .center .snd) in
      let p0 : Id B0 b0 b0' ≔ re0 .contrr a0 .contract (b0, r0) .fst in
      let p1 : Id B1 b1 b1' ≔ re1 .contrr a1 .contract (b1, r1) .fst in
      let q0 : Id (R0 a0) p0 r0 r0'
        ≔ re0 .contrr a0 .contract (b0, r0) .snd in
      let q1 : Id (R1 a1) p1 r1 r1'
        ≔ re1 .contrr a1 .contract (b1, r1) .snd in
      (refl S p0 p1 q0 q1 .trl u,
       v2 ↦
         let w
           ≔ re2
               .contrr a2
               .contract {(b0, r0)} {(b1, r1)} (v2 .fst, v2 .snd) in
         S⁽ᵉᵉ⁾ (sym (refl p0)) (sym (refl p1)) (sym (refl q0))
             (sym (refl q1)) {v2} {u} (sym w .fst, sym w .snd)
             (refl S p0 p1 q0 q1 .liftl u)
           .trl (refl u)),
    contrl ≔ b2 ↦
      let S : (x0 : A0) (x1 : A1) → R0 x0 b0 → R1 x1 b1 → Type
        ≔ x0 x1 z0 z1 ↦ Σ (A2 x0 x1) (x2 ↦ R2 x2 b2 z0 z1) in
      let a0' : A0 ≔ re0 .contrl b0 .center .fst in
      let a1' : A1 ≔ re1 .contrl b1 .center .fst in
      let r0' : R0 a0' b0 ≔ re0 .contrl b0 .center .snd in
      let r1' : R1 a1' b1 ≔ re1 .contrl b1 .center .snd in
      let u : S a0' a1' r0' r1' ≔ (
        re2 .contrl b2 .center .fst,
        re2 .contrl b2 .center .snd) in
      let p0 : Id A0 a0 a0' ≔ re0 .contrl b0 .contract (a0, r0) .fst in
      let p1 : Id A1 a1 a1' ≔ re1 .contrl b1 .contract (a1, r1) .fst in
      let q0 : Id R0 p0 (refl b0) r0 r0'
        ≔ re0 .contrl b0 .contract (a0, r0) .snd in
      let q1 : Id R1 p1 (refl b1) r1 r1'
        ≔ re1 .contrl b1 .contract (a1, r1) .snd in
      (refl S p0 p1 q0 q1 .trl u,
       v2 ↦
         let w
           ≔ re2
               .contrl b2
               .contract {(a0, r0)} {(a1, r1)} (v2 .fst, v2 .snd) in
         S⁽ᵉᵉ⁾ (sym (refl p0)) (sym (refl p1)) (sym (refl q0))
             (sym (refl q1)) {v2} {u} (sym w .fst, sym w .snd)
             (refl S p0 p1 q0 q1 .liftl u)
           .trl (refl u)))

{` This gives the coinductive case in a proof that any 1-1 correspondence is a bisimulation. `}
  def ⇨bisim (A B : Type) (R : A → B → Type) (re : is11 A B R)
    : isBisim A B R
    ≔ [
  | .trr ↦ a ↦ re .contrr a .center .fst
  | .liftr ↦ a ↦ re .contrr a .center .snd
  | .trl ↦ b ↦ re .contrl b .center .fst
  | .liftl ↦ b ↦ re .contrl b .center .snd
  | .id.e ↦ a0 b0 r0 a1 b1 r1 ↦
      ⇨bisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ (R.2 a2 b2 r0 r1))
        (of_Id A.0 A.1 A.2 B.0 B.1 B.2 R.0 re.0 R.1 re.1 R.2 re.2 a0 a1 b0
           b1 r0 r1)]

end

{` Finally, we can put this all together to show that any quasi-invertible map induces an equality of types. `}
def ua (A B : Type) (f : A → B) (g : B → A)
  (η : (a : A) → Id A (g (f a)) a) (ε : (b : B) → Id B (f (g b)) b)
  : Id Type A B
  ≔ glue A B (a b ↦ Id B (f a) b)
      (is11.⇨bisim A B (a b ↦ Id B (f a) b)
         (contrr ≔ a ↦ is_contr.id_from B (f a),
          contrl ≔ qinv.is_contr_fiber A B f (g, η, ε)))

{` convenience `}
def ua_qinv (A B : Type) (f : A → B) (qinv_f : qinv A B f) : Id Type A B
  ≔ ua A B f (qinv_f .fro) (qinv_f .fro_to) (qinv_f .to_fro)

{` Equivalences are maps with contractible fibers `}

def fiber (A B : Type) (f : A → B) (b : B) : Type ≔ Σ A (a ↦ Id B (f a) b)

def is_equiv (A B : Type) (f : A → B) : Type
  ≔ (b : B) → is_contr (fiber A B f b)

def qinv_to_equiv (A B : Type) (f : A → B) (qinv_f : qinv A B f)
  : is_equiv A B f
  ≔ qinv.is_contr_fiber A B f qinv_f

def Equiv (A B : Type) : Type ≔ Σ (A → B) (is_equiv A B)

def Iso (A B : Type) : Type ≔ Σ (A → B) (f ↦ qinv A B f)

def corr11 (A B : Type) : Type ≔ Σ (A → B → Type) (R ↦ is11 A B R)

{` Finally, any equivalence induces an equality of types `}

def ua_equiv (A B : Type) (e : Σ (A → B) (f ↦ is_equiv A B f))
  : Id Type A B
  ≔
  let f ≔ e .fst in
  let is_equiv_f ≔ e .snd in
  glue A B (a b ↦ Id B (f a) b)
    (is11.⇨bisim A B (a b ↦ Id B (f a) b)
       (contrr ≔ a ↦ is_contr.id_from B (f a), contrl ≔ is_equiv_f))

def ua_11 (A B : Type) (R_11 : corr11 A B) : Id Type A B
  ≔ glue A B (R_11 .fst) (is11.⇨bisim A B (R_11 .fst) (R_11 .snd))

{` Propositions `}

def is_prop (A : Type) : Type ≔ (x y : A) → Id A x y

section is_prop ≔

  def loop＝refl (A : Type) (pA : is_prop A) (x : A) (p : Id A x x)
    : Id (Id A x x) p (refl x)
    ≔ sym
        (refl
             ((z : A) (q : Id A x z) (r : Id A x z) ↦ A⁽ᵉᵉ⁾ p (refl z) q r)
             (pA x x) (coconn A x x (pA x x)) (coconn A x x (pA x x))
         .trl (ap pA p (refl x)))

end

{` (h)-Sets `}

def is_set (A : Type) : Type ≔ (x y : A) → is_prop (Id A x y)

def is_prop⇨is_set (A : Type) (pA : is_prop A) : is_set A
  ≔ x y p q ↦
    J A x (y q ↦ (p : Id A x y) → Id (Id A x y) p q)
      (p ↦ is_prop.loop＝refl A pA x p) y q p

{` Any square in a set can be filled. `}
def is_set.sq (A : Type) (sA : is_set A) (x00 x01 : A) (x02 : Id A x00 x01)
  (x10 x11 : A) (x12 : Id A x10 x11) (x20 : Id A x00 x10)
  (x21 : Id A x01 x11)
  : Id (Id A) x02 x12 x20 x21
  ≔ A⁽ᵉᵉᵉ⁾ (coconn A x00 x01 x02) (coconn A x10 x11 x12) (refl x20)
        (A⁽ᵉᵉ⁾ x02 x12 .liftl x21)
      .trr (sA x00 x10 x20 (A⁽ᵉᵉ⁾ x02 x12 .trl x21))

{` Proof that ua is an equivalence, suggested by Mike:
Σ Type (Equiv A) ≃ Σ Type (Id Type A) ≃ 1, since Equiv A B is a retract of Id Type A B
So Equiv A B ≃ Id Type A B
`}

def Σ_fib_fam_iso (A : Type) (B : A → Type) (a : A)
  : Iso (B a) (Σ (Σ A B) (x ↦ Id A a (x .fst)))
  ≔ (
  fst ≔ b ↦ ((a, b), refl a),
  snd ≔ (
    fro ≔ x ↦
      let a' : A ≔ x .fst .fst in
      let b' : B a' ≔ x .fst .snd in
      let a'≡a : Id A a a' ≔ x .snd in
      ap B a'≡a .trl b',
    fro_to ≔ b ↦ refl B (refl a) .liftl b,
    to_fro ≔ y ↦
      let a' : A ≔ y .fst .fst in
      let b' : B a' ≔ y .fst .snd in
      let a'≡a : Id A a a' ≔ y .snd in
      ((a'≡a, ap B a'≡a .liftl b'), coconn A a a' a'≡a)))

def Σ_fib_fam_Id (A : Type) (B : A → Type) (a : A)
  : Id Type (B a) (Σ (Σ A B) (x ↦ Id A a (x .fst)))
  ≔
  let iso : Iso (B a) (Σ (Σ A B) (x ↦ Id A a (x .fst)))
    ≔ Σ_fib_fam_iso A B a in
  ua (B a) (Σ (Σ A B) (x ↦ Id A a (x .fst))) (iso .fst) (iso .snd .fro)
    (iso .snd .fro_to) (iso .snd .to_fro)

def equiv_triangle_to_Id_map (A B C : Type) (f : A → B) (g : B → C)
  (h : A → C) (qinv_f : qinv A B f) (p : Id (A → C) h (a ↦ g (f a)))
  : Id (Σ Type (X ↦ X → C)) (A, h) (B, g)
  ≔
  let q : Id Type A B ≔ ua_qinv A B f qinv_f in
  let qf
    : (q' : Id Type A B) (a : A) (b : B) (x2 : q' a b)
      → Id C (g (q' .trr a)) (g b)
    ≔ q' a b x2 ↦
      inverse C (g b) (g (q' .trr a))
        (ap g (sym (refl q') x2 (q' .liftr a) .trr (refl a))) in
  (q,
   𝑥 ⤇
     concat C (h 𝑥.0) (g (f 𝑥.0)) (g 𝑥.1) (p (refl 𝑥.0)) (qf q 𝑥.0 𝑥.1 𝑥.2))

def Id_Σ_Id_fam (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (qinv_Σf : qinv (Σ A B) (Σ A C) (Σ.functor_fiber A B C f))
  : Id (A → Type) B C
  ≔
  let triangle
    : Id (Σ A B → A) (x ↦ x .fst)
        ((x : Σ A B) ↦ ((x .fst, f (x .fst) (x .snd)) : Σ A C) .fst)
    ≔ refl _ in
  let Id_Σ_maps
    : Id (Σ Type (X ↦ X → A)) (Σ A B, x ↦ x .fst) (Σ A C, x ↦ x .fst)
    ≔ equiv_triangle_to_Id_map (Σ A B) (Σ A C) A (Σ.functor_fiber A B C f)
        (x ↦ x .fst) (x ↦ x .fst) qinv_Σf triangle in
  let Id_fib
    : (a : A)
      → Id Type (Σ (Σ A B) (x ↦ Id A a (x .fst)))
          (Σ (Σ A C) (x ↦ Id A a (x .fst)))
    ≔ a ↦
      ap
        ((map : Σ Type (X ↦ X → A)) ↦
         Σ (map .fst) (x ↦ Id A a (map .snd x))) Id_Σ_maps in
  funext A Type B C
    (a ↦
     concat Type (B a) (Σ (Σ A B) (x ↦ Id A a (x .fst))) (C a)
       (Σ_fib_fam_Id A B a)
       (concat Type (Σ (Σ A B) (x ↦ Id A a (x .fst)))
          (Σ (Σ A C) (x ↦ Id A a (x .fst))) (C a) (Id_fib a)
          (inverse Type (C a) (Σ (Σ A C) (x ↦ Id A a (x .fst)))
             (Σ_fib_fam_Id A C a))))

def Σ_Id_prop (A : Type) (B : A → Type)
  (is_prop_B : (a : A) → is_prop (B a)) (a a' : A) (b : B a) (b' : B a')
  (p : Id A a a')
  : Id (Σ A B) (a, b) (a', b')
  ≔ (
  p,
  ap ((y : B a') ↦ ap B p b y) (is_prop_B a' (ap B p .trr b) b')
    .trr (ap B p .liftr b))

{` *Retractions and Retracts* `}

{` f and g form a section-retraction of B onto A `}

def is_retraction (A B : Type) (f : A → B) (g : B → A) : Type
  ≔ (a : A) → Id A (g (f a)) a

{` type of retractions of f `}

def retraction (A B : Type) (f : A → B) : Type
  ≔ Σ (B → A) (is_retraction A B f)

{` A is a retract of B `}
def retract (B A : Type) : Type ≔ Σ (A → B) (retraction A B)

def Σ_is_retraction (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (g : (a : A) → C a → B a)
  (fib_is_retraction : (a : A) → is_retraction (B a) (C a) (f a) (g a))
  : is_retraction (Σ A B) (Σ A C) (Σ.functor_fiber A B C f)
      (Σ.functor_fiber A C B g)
  ≔ x ↦ (refl _, fib_is_retraction (x .fst) (x .snd))

def Σ_retraction (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (fib_retraction : (a : A) → retraction (B a) (C a) (f a))
  : retraction (Σ A B) (Σ A C) (Σ.functor_fiber A B C f)
  ≔
  let g : (a : A) → C a → B a ≔ a ↦ fib_retraction a .fst in
  let fib_is_retraction : (a : A) → is_retraction (B a) (C a) (f a) (g a)
    ≔ a ↦ fib_retraction a .snd in
  (fst ≔ Σ.functor_fiber A C B g,
   snd ≔ Σ_is_retraction A B C f g fib_is_retraction)

def Σ_retract (A : Type) (C B : A → Type)
  (fib_retract : (a : A) → retract (C a) (B a))
  : retract (Σ A C) (Σ A B)
  ≔
  let f : (a : A) → B a → C a ≔ a ↦ fib_retract a .fst in
  let fib_retraction : (a : A) → retraction (B a) (C a) (f a)
    ≔ a ↦ fib_retract a .snd in
  let g : (a : A) → C a → B a ≔ a ↦ fib_retraction a .fst in
  let fib_is_retraction : (a : A) → is_retraction (B a) (C a) (f a) (g a)
    ≔ a ↦ fib_retraction a .snd in
  (fst ≔ Σ.functor_fiber A B C f,
   snd ≔ Σ_retraction A B C f fib_retraction)

def retract_contr_contr (A B : Type) (f : retract B A) (b : is_contr B)
  : is_contr A
  ≔ (
  center ≔ f .1 .0 (b .0),
  contract ≔ a ↦ calc
    a
    = (f .1 .0 (f .0 a))
        by inverse A (f .1 .0 (f .0 a)) a (f .1 .1 a)
    = (f .1 .0 (b .0))
        by ap (f .1 .0) (b .1 (f .0 a)) ∎)

def id_to_qinv (A B : Type) (P : Id Type A B) : Σ (A → B) (f ↦ qinv A B f)
  ≔ (
  fst ≔ P .trr,
  snd ≔ (
    fro ≔ P .trl,
    fro_to ≔ a ↦
      sym (refl P) (P .liftl (P .trr a)) (P .liftr a)
        .trl (refl (P .trr a)),
    to_fro ≔ b ↦
      sym (refl P) (P .liftr (P .trl b)) (P .liftl b)
        .trr (refl (P .trl b))))

def id_to_equiv (A B : Type) (P : Id Type A B)
  : Σ (A → B) (f ↦ is_equiv A B f)
  ≔ (
  fst ≔ id_to_qinv A B P .fst,
  snd ≔ qinv_to_equiv A B (id_to_qinv A B P .fst) (id_to_qinv A B P .snd))

`from anor:
def is_contr_Σ_Id (A : Type) (a : A) : is_contr (Σ A (a' ↦ Id A a' a)) ≔ (
  center ≔ (a, refl a),
  contract ≔ a0_a2 ↦
    let a0 ≔ a0_a2 .fst in
    let a2 ≔ a0_a2 .snd in
    (a2, conn A a0 a a2))

def Σ_ind (A : Type) (B : A → Type) (C : (Σ A B) → Type)
  : ((x : A) → (y : B x) → C (fst ≔ x, snd ≔ y)) → (x : Σ A B) → C x
  ≔ f y ↦ f (y .fst) (y .snd)

def is_contr_lemma (A : Type) : (is_contr A) → Σ A (_ ↦ is_prop A) ≔ x ↦ (
  fst ≔ x .center,
  snd ≔ x' y ↦ calc
    x'
    = (x .center)
        by (x .contract) x'
    = y
        by inverse A y (x .center) (x .contract y) ∎)

def is_prop_fam_is_prop_sections (A : Type) (B : A → Type)
  : (is_prop A) → ((a : A) → is_prop (B a)) → is_prop ((a : A) → B a)
  ≔ p q f g ↦ a ⤇
    J A a.0 (a' p' ↦ Id B p' (f a.0) (g a')) (q a.0 (f a.0) (g a.0)) a.1
      a.2

def is_contr_is_prop (A : Type) : is_prop (is_contr A) ≔ x y ↦ (
  center ≔ y .contract (x .center),
  contract ≔ a ⤇
    `any square in a set can be filled, and A is a set since A is a prop since A is contractible.
    let H : is_prop A ≔ (is_contr_lemma A x .snd) in
    is_set.sq A (is_prop⇨is_set A H) a.0 a.1 a.2 (x .center) (y .center)
      (y .contract (x .center)) (x .contract a.0) (y .contract a.1))

def is_contr_is_prop_hetero (A B : Type) (P : Id Type A B) (h : is_contr A)
  (k : is_contr B)
  : (Id is_contr) P h k
  ≔
  let fam : (is_contr A) → Type ≔ x ↦ refl is_contr P x k in
  let p : Id (is_contr A) h (refl is_contr P .trl k)
    ≔ is_contr_is_prop A h (refl is_contr P .trl k) in
  ap fam p .trl (ap is_contr P .liftl k)

` Equiv A B is a retract of Id Type A B
def retract_Id_Equiv (A B : Type) : retract (Id Type A B) (Equiv A B) ≔ (
  fst ≔ ua_equiv A B,
  snd ≔ (
    fst ≔ id_to_equiv A B,
    snd ≔ e ↦ (
      fst ≔ refl _,
      snd ≔ b ⤇
        let fam : B → Type ≔ x ↦ Σ A (a ↦ Id B (e .fst a) x) in
        is_contr_is_prop_hetero (Σ A (a ↦ Id B (e .fst a) b.0))
          (Σ A (a ↦ Id B (e .fst a) b.1)) (ap fam b.2)
          (id_to_equiv A B (ua_equiv A B e) .snd b.0) (e .snd b.1))))








