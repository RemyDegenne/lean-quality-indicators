namespace OAI

open Set Function Filter MeasureTheory Metric

open scoped ENNReal Topology Classical

noncomputable section

namespace CircleDomainRigidity

lemma hausdorff_one_fiber_le_liminf_cover
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y) (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (T : ℕ → ℕ → Set X) (hT : ∀ n k, ediam (T n k) ≤ r n)
    (hcover : ∀ n, A ⊆ ⋃ k, T n k) (y : Y) :
    (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤
      liminf (fun n => ∑' k, if y ∈ closure (f '' T n k) then ediam (T n k) else 0) atTop := by
  let S (n k : ℕ) := A ∩ f ⁻¹' {y} ∩ T n k
  have hS : ∀ n k, ediam (S n k) ≤ r n := fun n k =>
    (ediam_mono inter_subset_right).trans (hT n k)
  have hcov : ∀ n, A ∩ f ⁻¹' {y} ⊆ ⋃ k, S n k := by
    intro n x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover n hx.1)
    exact mem_iUnion.mpr ⟨k, hx, hk⟩
  have h := Measure.hausdorffMeasure_le_liminf_tsum 1 (A ∩ f ⁻¹' {y}) r hr S
    (.of_forall hS) (.of_forall hcov)
  simp only [ENNReal.rpow_one] at h
  apply h.trans
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  apply ENNReal.tsum_le_tsum
  intro k
  split_ifs with hy
  · exact ediam_mono inter_subset_right
  · have hempty : S n k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxT⟩
      exact hy (subset_closure ⟨x, hxT, hx.2⟩)
    simp only [hempty, ediam_empty]
    exact le_rfl

end CircleDomainRigidity
end
end OAI
