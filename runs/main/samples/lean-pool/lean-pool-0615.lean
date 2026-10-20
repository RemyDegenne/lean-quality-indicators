@[expose] public section

noncomputable section

namespace EulerH6Nonlinear

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerVectorCylinder
  EulerJetProductBounds EulerSpatialSobolevInverse

open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

section FieldCalculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sobolev_add_le (q : ℕ) (f g : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ q, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) :
    liftSobolevNorm period q (f + g) ≤ liftSobolevNorm period q f + liftSobolevNorm period q g := by
  unfold liftSobolevNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  rw [word_add period w f g hf hg]
  have hfj := hfL2 j (by have := Finset.mem_range.1 hj; omega) w
  have hgj := hgL2 j (by have := Finset.mem_range.1 hj; omega) w
  have he := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfj.eLpNorm_ne_top, hgj.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa only [ENNReal.toReal_add hfj.eLpNorm_ne_top hgj.eLpNorm_ne_top] using he

end FieldCalculus
end EulerH6Nonlinear
end
end
