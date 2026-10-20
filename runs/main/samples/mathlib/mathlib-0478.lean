@[expose] public section

noncomputable section

open Set Function Filter Finset Metric Nat uniformity NNReal ENNReal

open scoped Topology

variable {α : Type*} {β : Type*} {ι : Type*}

section

variable {R : Type*} [TopologicalSpace R] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

theorem tendsto_nat_ceil_mul_div_atTop {a : R} (ha : 0 ≤ a) :
    Tendsto (fun x ↦ (⌈a * x⌉₊ : R) / x) atTop (𝓝 a) := by
  have A : Tendsto (fun x : R ↦ a + x⁻¹) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  rw [add_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    rw [le_div_iff₀ (zero_lt_one.trans_le hx)]
    exact Nat.le_ceil _
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    simp [div_le_iff₀ (zero_lt_one.trans_le hx), inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne',
      (Nat.ceil_lt_add_one (mul_nonneg ha (zero_le_one.trans hx))).le, add_mul]

end
end
end
