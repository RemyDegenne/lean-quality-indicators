public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open Matrix

variable {K : Type} [Field K] {d : ℕ}

theorem uScal_swap_entry (a b x y : Fin d) :
    Matrix.swap K a b x y = 0 ∨ Matrix.swap K a b x y = 1 := by
  simp only [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
end
