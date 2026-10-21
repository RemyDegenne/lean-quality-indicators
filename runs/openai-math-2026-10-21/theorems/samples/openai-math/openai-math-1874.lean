namespace OAI

section

section

section

section

section

section

section

section

section

section

noncomputable section

noncomputable section

namespace CannonMetricQC

open MeasureTheory Set Metric

open scoped ENNReal NNReal

lemma eLpNorm_two_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (g : X → E) (μ : Measure X) :
    (eLpNorm' g (2:ℝ) μ)^2=∫⁻ x, ‖g x‖ₑ^2 ∂μ := by
  simpa only [ENNReal.rpow_two] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f:=g) (μ:=μ) (by norm_num : (0:ℝ) < 2)).symm

end CannonMetricQC
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
