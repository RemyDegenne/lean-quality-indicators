public section

noncomputable section

open MeasureTheory Module

open scoped RealInnerProductSpace

namespace TauCeti

section coordinates

variable (p : ℕ)

theorem coe_symmetricBasis_diag (i : Fin p) :
    ((symmetricBasis p ⟨(i, i), le_rfl⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      Matrix (Fin p) (Fin p) ℝ) = Matrix.single i i 1 := by
  ext k l
  rw [Matrix.single_apply]
  rcases le_total k l with h | h
  · rw [coe_symmetricBasis_apply_of_le _ _ h]
    simp [Subtype.ext_iff, Prod.ext_iff]
  · rw [coe_symmetricBasis_apply_of_ge _ _ h]
    simp [Subtype.ext_iff, Prod.ext_iff, and_comm]

end coordinates
end TauCeti
end
end
