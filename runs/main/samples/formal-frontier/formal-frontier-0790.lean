@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

lemma circlePunctureIntersectionLinearVector_second_pos_of_component_false
    (t : unitInterval) (p : circlePunctureIntersection)
    (hp : circlePunctureIntersectionComponent p = false) :
    0 < circlePunctureIntersectionLinearVector t p 1 := by
  have hpy := (circlePunctureIntersectionComponent_eq_false_iff p).mp hp
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  simp only [circlePunctureIntersectionLinearVector, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [hp]
  simp only [circlePunctureIntersectionRepresentative_false_second, mul_one]
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht1)
      (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hpy)

end SphereTopology
end
end
