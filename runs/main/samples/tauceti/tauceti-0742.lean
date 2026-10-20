public section

namespace CliffordAlgebra

open TauCeti QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

theorem orthogonalSpinorNorm_negOrthogonal_smul_sq_eq_one_iff (a : Kˣ) :
    orthogonalSpinorNorm ((a : K) • QuadraticMap.sq) (QuadraticMap.nondegenerate_smul_sq a.ne_zero)
      (negOrthogonal _) = 1 ↔ IsSquare (a : K) := by
  rw [orthogonalSpinorNorm_negOrthogonal_smul_sq]
  simp [squareClassHom_apply, ← isSquare_units_val_iff]

end CliffordAlgebra
end
