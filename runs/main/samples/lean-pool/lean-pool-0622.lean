@[expose] public section

noncomputable section

namespace CKN.Core.Step4

theorem min_kappa_pos {q τ : ℝ} (hτ : 0 < τ) (hq : 0 < q) : 0 < min ((1 / τ + 8 / 25)⁻¹) q := by
  have hkappa : 0 < (1 / τ + 8 / 25)⁻¹ := by
    have hsum : 0 < 1 / τ + 8 / 25 := by positivity
    exact inv_pos.mpr hsum
  exact lt_min hkappa hq

end CKN.Core.Step4
end
end
