public section

open MeasureTheory Set Filter

open scoped ENNReal Topology

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

theorem blowupLimitClauses_restrict_prod_eq (C : Set Vec3) (I : Set ℝ) :
    (volume : Measure ParabolicPoint).restrict (spaceTimeSet C I) =
      (volume.restrict C).prod (volume.restrict I) := by
  rw [Measure.prod_restrict]
  rfl

end ESS
end
end
