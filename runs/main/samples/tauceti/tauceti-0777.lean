public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} {E F : ι → Type*}

variable [∀ i, SeminormedAddCommGroup (E i)]

section PseudoMetricSpace

variable [Fact (1 ≤ p)] {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]

theorem dist_le_sqrt_card_mul_dist_ofLp (x y : PiLp 2 β) :
    dist x y ≤ Real.sqrt (Fintype.card ι) * dist (WithLp.ofLp x) (WithLp.ofLp y) := by
  simpa [NNReal.coe_rpow, Real.sqrt_eq_rpow] using
    (lipschitzWith_toLp 2 β).dist_le_mul (WithLp.ofLp x) (WithLp.ofLp y)

end PseudoMetricSpace
end PiLp
end
