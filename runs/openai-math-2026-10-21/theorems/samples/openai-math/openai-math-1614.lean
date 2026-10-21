namespace OAI

open Set Function MeasureTheory

open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_regular_level
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hcompact : HasCompactSupport f) (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    (hq2 : (∫⁻ z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, IsPlanarRegularValue f t ∧ weightedScalarLevelLength D f q t < ∞ := by
  have hc := hcoarea D hD f (hf.of_le (by simp)).contDiffOn q hq
  have hfin := weighted_scalar_coarea_integral_lt_top hc hq hq2 hf2
  have hbad : volume {t | weightedScalarLevelLength D f q t = ∞} = 0 := by
    have ha := ae_lt_top' hc.1 hfin.ne
    rw [ae_iff] at ha
    simpa only [not_lt, top_le_iff] using ha
  have hcrit := hsard f hf hcompact
  have hnull : volume ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞}) = 0 := measure_union_null hcrit hbad
  have hpositive : 0 < volume (Ioo a b \ ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞})) := by
    rw [measure_sdiff_null hnull, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  obtain ⟨t, ht, hgood⟩ := nonempty_of_measure_ne_zero hpositive.ne'
  refine ⟨t, ht, ?_, ?_⟩
  · intro z hz hzero
    exact hgood (Or.inl ⟨z, hzero, hz⟩)
  · exact lt_top_iff_ne_top.mpr (fun ht => hgood (Or.inr ht))

end CircleDomainRigidity
end
end OAI
