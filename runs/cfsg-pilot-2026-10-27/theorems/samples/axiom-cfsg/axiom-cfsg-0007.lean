public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution

open scoped MatrixGroups

variable {K : Type} [Field K]

theorem quadOdd_tauA₂ : quadOdd 3 K (tauA₂ K) = 1 := by
  rw [tauA₂, Frame.Q_incl, Matrix.det_fin_two_of]
  ring

end CFSG.ComponentClassification.HarrisLit.T1
end
