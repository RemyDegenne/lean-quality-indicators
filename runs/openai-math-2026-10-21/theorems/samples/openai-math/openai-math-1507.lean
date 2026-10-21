namespace OAI

noncomputable section

namespace Kaplansky

section

variable {E F G : Type*}
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [AddCommGroup G] [Module ℂ G] [Module ℝ G] [IsScalarTower ℝ ℂ G]

theorem complexDerivativeSign_complex_equiv (e d : E ≃ₗ[ℂ] F) :
    complexDerivativeSign e (d.toLinearMap.restrictScalars ℝ) = 1 := by
  apply sign_pos
  exact real_det_complex_equiv_pos (d.trans e.symm)

end
end Kaplansky
end
end OAI
