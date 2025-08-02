import "univalence"

def 𝔹 : Type ≔ data [ t. | f. ]

def flip : 𝔹 → 𝔹 ≔ [ t. ↦ f. | f. ↦ t. ]

def flips (x y : 𝔹) : Type ≔ match x, y [
| t., f. ↦ sig #(transparent) ()
| t., t. ↦ data []
| f., f. ↦ data []
| f., t. ↦ sig #(transparent) ()]

def flips_tb (b : 𝔹) (f : flips t. b)
  : refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips t. b} {b ↦ flips t. b}
      (b ⤇ Id flips {t.} {t.} t. b.2) (b, f) (f., ())
  ≔ match b [ t. ↦ match f [ ] | f. ↦ (f., ()) ]

def flips_fb (b : 𝔹) (f : flips f. b)
  : refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips f. b} {b ↦ flips f. b}
      (b ⤇ Id flips {f.} {f.} f. b.2) (b, f) (t., ())
  ≔ match b [ f. ↦ match f [ ] | t. ↦ (t., ()) ]

def flips_bt (b : 𝔹) (f : flips b t.)
  : refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips b t.} {b ↦ flips b t.}
      (b ⤇ Id flips b.2 {t.} {t.} t.) (b, f) (f., ())
  ≔ match b [ t. ↦ match f [ ] | f. ↦ (f., ()) ]

def flips_bf (b : 𝔹) (f : flips b f.)
  : refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips b f.} {b ↦ flips b f.}
      (b ⤇ Id flips b.2 {f.} {f.} f.) (b, f) (t., ())
  ≔ match b [ f. ↦ match f [ ] | t. ↦ (t., ()) ]

def flips11 : is11 𝔹 𝔹 flips ≔ (
  contrr ≔ [
  | t. ↦ ((f., ()), a ↦ flips_tb (a .fst) (a .snd))
  | f. ↦ ((t., ()), a ↦ flips_fb (a .fst) (a .snd))],
  contrl ≔ [
  | t. ↦ ((f., ()), a ↦ flips_bt (a .fst) (a .snd))
  | f. ↦ ((t., ()), a ↦ flips_bf (a .fst) (a .snd))])

def 𝔽 : Id Type 𝔹 𝔹 ≔ glue 𝔹 𝔹 flips (bisim_of_11 𝔹 𝔹 flips flips11)

echo 𝔽 .trr t.

def 𝔽t : Id 𝔹 (𝔽 .trr t.) f. ≔ refl _

echo 𝔽 .trl f.

def 𝔽f : Id 𝔹 (𝔽 .trr f.) t. ≔ refl _

echo 𝔽 .liftr t.

def 𝔽lt : Id (𝔽 t. f.) (𝔽 .liftr t.) ((),) ≔ refl _

echo 𝔽 .liftr f.

def 𝔽lf : Id (𝔽 f. t.) (𝔽 .liftr f.) ((),) ≔ refl _
