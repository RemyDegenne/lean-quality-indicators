namespace OAI

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem scalarBlockHom_single {n : ℕ} (i j : Fin n) (z : ℂ) :
    F.scalarBlockHom n (CStarMatrix.ofMatrix (Matrix.single i j z)) = z • F.entry i j := by
  rw [F.scalarBlockHom_apply]
  simp [CStarMatrix.ofMatrix_apply, Matrix.single_apply, ite_smul, ite_and]

end FullMatrixCorner
end
end KadisonKastler
end OAI
