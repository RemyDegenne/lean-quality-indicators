@[expose] public section

noncomputable section

open Set Function Filter Finset Metric Module Asymptotics Nat

open scoped Topology Ring

variable {α : Type*}

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}
  [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [_i : OrderTopology S]

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

theorem Antitone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

end
end
end
