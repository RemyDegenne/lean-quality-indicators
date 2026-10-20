public section

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix

namespace TauCeti

variable (p : ℕ)

theorem lowerTriangleGram_image_posDiagLowerRegion :
    lowerTriangleGram p '' posDiagLowerRegion p =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  ext A
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← coe_choleskyReconstruction_posDiagOfMem p hx]
    exact (choleskyReconstruction (posDiagOfMem p hx)).2
  · intro hA
    refine ⟨fun ij => (cholesky ⟨A, hA⟩).1 ij.1.1 ij.1.2, fun i => (cholesky ⟨A, hA⟩).2.2 i, ?_⟩
    refine Subtype.ext ?_
    rw [coe_lowerTriangleGram, lowerTriangleMatrix_entries (cholesky ⟨A, hA⟩).2.1]
    exact cholesky_mul_transpose ⟨A, hA⟩

end TauCeti
end
end
