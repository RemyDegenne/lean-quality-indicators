public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

open scoped ComplexOrder in
theorem schwarzChristoffelBoundary_lt_vertexAtInfinity (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p : ℝ} (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ p < schwarzChristoffelVertexAtInfinity a e z₀ := by
  refine lt_of_le_of_ne ?_
    (schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_le a e z₀ hp ha hS)
  have hsum : ∀ {q : ℝ}, p ≤ q → -1 < ∑ i with a i = q, e i := fun hq ↦ by
    simpa using
      Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (β := ℝ) (a := a) (e := e)
        (p := p) (c := -1) Finset.univ (by norm_num) (by simpa using hp) (by simpa using ha) hq
  have hangle : schwarzChristoffelEdgeAngle a e p = 0 := by
    rw [schwarzChristoffelEdgeAngle_eq_sum_filter, Finset.sum_filter, Finset.sum_eq_zero,
      mul_zero]
    intro i _
    rcases eq_or_ne (e i) 0 with hei | hei
    · simp [hei]
    · simp [not_lt.mpr (ha i hei)]
  have hBtop : Tendsto (schwarzChristoffelBoundary a e z₀) atTop
      (𝓝 (schwarzChristoffelVertexAtInfinity a e z₀)) := by
    apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hS tendsto_abs_atTop_atTop
    filter_upwards [eventually_ge_atTop p] with x hx
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hsum hx)
  apply ge_of_tendsto hBtop
  filter_upwards [eventually_ge_atTop p] with x hx
  have h := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀
    (fun i hi hmem ↦ (ha i hi).not_gt hmem.1) hp (hsum hx) ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ hx
  rw [hangle, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h
  exact sub_nonneg.mp (h ▸ Complex.zero_le_real.mpr (norm_nonneg _))

end TauCeti
end
end
