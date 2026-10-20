public section

open Matrix TauCeti

namespace Matrix.SpecialLinearGroup

universe u

noncomputable section

variable {k : Type u} {n : ℕ}

section IsCancelMulZero

variable [CommRing k] [IsCancelMulZero k]

/-- **The Weyl group of the diagonal torus of `SL_n(k)`**: when the determinant-one diagonal
torus separates coordinates, its normalizer modulo the torus is canonically the symmetric group
on the coordinate lines. -/
def diagonalNormalizerQuotientMulEquivPerm
    (hsep : DiagonalTorusSeparatesCoordinates k n) :
    Subgroup.normalizerQuotient (diagonalTorus k n) ≃* Equiv.Perm (Fin n) := by
  let φ := diagonalNormalizerPerm (k := k) (n := n) hsep
  have hkill : ∀ g : Subgroup.normalizer
      (diagonalTorus k n : Set (SpecialLinearGroup (Fin n) k)),
      (g : SpecialLinearGroup (Fin n) k) ∈ diagonalTorus k n → φ g = 1 :=
    fun g hg ↦ (diagonalNormalizerPerm_eq_one_iff hsep g).mpr hg
  apply MulEquiv.ofBijective (Subgroup.normalizerQuotientLift (diagonalTorus k n) φ hkill)
  constructor
  · exact (Subgroup.normalizerQuotientLift_injective_iff
      (diagonalTorus k n) φ hkill).mpr (diagonalNormalizerPerm_eq_one_iff hsep)
  · exact Subgroup.normalizerQuotientLift_surjective_of_surjective
      (diagonalTorus k n) φ hkill (diagonalNormalizerPerm_surjective hsep)

end IsCancelMulZero
end
end Matrix.SpecialLinearGroup
end
