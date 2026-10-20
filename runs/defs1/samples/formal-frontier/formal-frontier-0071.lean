@[expose] public section

universe uR uS uT uι uκ uν

open Function

open scoped Matrix

namespace Module

section Rectangular

variable (R : Type uR) [Semiring R]

variable (ι : Type uι) [Fintype ι] (κ : Type uκ)

variable {S : Type uS} [Semiring S]

/-- Transport a specified equivalence and its specified inverse. Both coordinate
sets are finite, but their cardinalities need not agree. Inverse identities are
mapped entrywise, then Mathlib's rectangular inverse constructor is reused. -/
noncomputable def rightFreeScalarExtensionEquiv [Fintype κ]
    (f : R →+* S) (e : (ι → R) ≃ₗ[Rᵐᵒᵖ] (κ → R)) :
    (ι → S) ≃ₗ[Sᵐᵒᵖ] (κ → S) := by
  classical
  let e' := (rightFreeCoordEquiv R ι).trans (e.trans (rightFreeCoordEquiv R κ).symm)
  let A := LinearMap.toMatrixRight' e'.toLinearMap
  let B := LinearMap.toMatrixRight' e'.symm.toLinearMap
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← LinearMap.toMatrixRight'_comp, e'.symm_comp, LinearMap.toMatrixRight'_id]
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← LinearMap.toMatrixRight'_comp, e'.comp_symm, LinearMap.toMatrixRight'_id]
  have hAB' : A.map (RingHom.op f) * B.map (RingHom.op f) = 1 := by
    rw [← Matrix.map_mul, hAB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBA' : B.map (RingHom.op f) * A.map (RingHom.op f) = 1 := by
    rw [← Matrix.map_mul, hBA]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact (rightFreeCoordEquiv S ι).symm.trans
    ((Matrix.toLinearEquivRight'OfInv hBA' hAB').trans (rightFreeCoordEquiv S κ))

end Rectangular
end Module
end
