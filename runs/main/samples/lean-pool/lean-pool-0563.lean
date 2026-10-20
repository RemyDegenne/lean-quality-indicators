public section

open CKN CKN.Foundation.Parabolic

open Set

open scoped Topology

noncomputable section

namespace CKN

local instance gaussDerivativesNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance gaussDerivativesNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

theorem gaussCarlemanPhase_scalarLaplacian (q : ℝ)
    (z : ParabolicPoint) (ht : 0 < z.2) :
    scalarLaplacian (gaussCarlemanPhase q) z = -3 / (4 * z.2) := by
  rw [scalarLaplacian]
  simp_rw [gaussCarlemanPhase_spatialSecondPartial q z ht]
  simp
  ring

end CKN
end
end
