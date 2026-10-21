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

open MeasureTheory Set Metric Filter

open scoped ENNReal NNReal Topology

lemma cutoff_hasCompactSupport (χ : ℂ → ℂ) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → χ x=0) : HasCompactSupport χ := by
  apply (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport χ)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hh
  have hz := hs x (by simpa [mem_closedBall,dist_zero_right,not_le] using hh)
  exact hx hz

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
