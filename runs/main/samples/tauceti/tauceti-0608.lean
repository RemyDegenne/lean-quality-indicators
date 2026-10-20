public section

namespace Matrix

universe u

variable {m n : Type*} {R : Type u} [CommRing R]

section Principal

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem principalMinor_submatrix (A : Matrix κ κ R) (e : ι ↪ κ) (s : Finset ι) :
    (A.submatrix e e).principalMinor s = A.principalMinor (s.map e) := by
  rw [principalMinor_def, principalMinor_def,
    ← det_submatrix_equiv_self (s.equivMap e) (A.submatrix Subtype.val Subtype.val),
    submatrix_submatrix, submatrix_submatrix]
  rfl

end Principal
end Matrix
end
