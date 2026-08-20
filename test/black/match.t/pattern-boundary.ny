def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def P : Type ≔ data [ pair. (x : ℕ) (y : ℕ) ]

{` The pattern variables of a higher-dimensional match are ordinarily cube variables,
introduced by ⤇, whose boundary is accessed with face suffixes. `}
def bar (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [
| zero. ⤇ 0
| suc. n ⤇ n.0]

{` But, as for abstractions, the boundary variables can also be named explicitly, in braces,
in which case the branch is introduced by ↦. `}
def bar′ (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [
| zero. ↦ 0
| suc. {m0} {m1} m2 ↦ m0]

echo bar′

about bar′

{` The two elaborate to the same term, and a stuck one displays with the pattern variables
that its branch recorded. `}
axiom a0 : ℕ

axiom a1 : ℕ

axiom a2 : Id ℕ a0 a1

about (bar a0 a1 a2)

about (bar′ a0 a1 a2)

{` But a definition that gets degenerated has pattern variables of a larger dimension than
the boundary variables it recorded, so those revert to being displayed as cube variables,
named after their top faces. `}
about (refl bar′)

{` A boundary variable can be a placeholder, and can be matched on further just like any
other pattern variable. `}
def baz (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [
| zero. ↦ 0
| suc. {m0} {_} m2 ↦ match m0 [ zero. ↦ 1 | suc. k ↦ k ]]

about baz

{` Each argument of a constructor decides separately whether to name its boundary; but if
any of them is left as a cube variable, the branch still uses ⤇. `}
def qux (y0 y1 : P) (y2 : Id P y0 y1) : ℕ ≔ match y2 [
| pair. {a0} {a1} a2 b ⤇ b.0]

about qux

{` It works at higher dimensions too, where the boundary variables come in the same order
as the boundary arguments of the corresponding constructor application. `}
def quux (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2⁽ᵉ⁾ [
| zero. ↦ 0
| suc. {m00} {m01} {m02} {m10} {m11} {m12} {m20} {m21} m22 ↦ m00]

about quux

{` Deep matches can name the boundaries at every level. `}
def deep (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [
| zero. ↦ 0
| suc. {m0} {m1} (zero.) ↦ m0
| suc. {m0} {m1} (suc. {k0} {k1} k2) ↦ k1]

about deep

{` As can multiple matches, whose other discriminees can be zero-dimensional. `}
def multi (x : ℕ) (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match x, y2 [
| zero., zero. ↦ 0
| zero., suc. {m0} {m1} m2 ↦ m0
| suc. _, zero. ↦ 1
| suc. _, suc. {n0} {n1} n2 ↦ n1]

about multi
