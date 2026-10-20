public section

open QuadraticMap

namespace QuadraticMap.IsometryEquiv

universe u v w

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The equivalence of Spin groups induced by a quadratic isometry equivalence. -/
def spinGroupEquiv (e : Q₁.IsometryEquiv Q₂) : spinGroup Q₁ ≃* spinGroup Q₂ :=
  MonoidHom.toMulEquiv e.toIsometry.spinGroupMap e.symm.toIsometry.spinGroupMap
    (by
      rw [QuadraticMap.Isometry.spinGroupMap_comp]
      have h : e.symm.toIsometry.comp e.toIsometry = QuadraticMap.Isometry.id Q₁ := by
        ext m
        exact e.symm_apply_apply m
      rw [h, QuadraticMap.Isometry.spinGroupMap_id])
    (by
      rw [QuadraticMap.Isometry.spinGroupMap_comp]
      have h : e.toIsometry.comp e.symm.toIsometry = QuadraticMap.Isometry.id Q₂ := by
        ext m
        exact e.apply_symm_apply m
      rw [h, QuadraticMap.Isometry.spinGroupMap_id])

end QuadraticMap.IsometryEquiv
end
