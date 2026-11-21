import "modalprelude"

` A modal typed binder
echo (x :♭| A) ⊗ B x
echo A ⊗ C

` A plain binder accepts a modal ascription
echo ∃ x, B x
echo ∃ (x :♭| A), B x

` A composite modality is compared by its generators, and displayed like the modalities in terms
echo (x :♭♯| A) ⊠ B x
echo (x :♭ ♯| A) ⊠ B x
