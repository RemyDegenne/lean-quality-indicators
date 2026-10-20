namespace P2MW.S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt

open MeasureTheory Set Filter Topology

noncomputable section

namespace Complex

namespace GreenFD

p2m_open

section Hyp

variable (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
  (hDU : D ⊆ U) (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
  (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
  (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im))

lemma mem_D_neg_r {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) (hy1 : y ≤ 1) : (⟨-r y, y⟩ : ℂ) ∈ D := by
  have hy0 : 0 ≤ y := sqrt3_pos.le.trans hy
  refine mk_mem_D ?_ (by rw [h_neg]; exact (h_r hy0 hy1).le)
  rw [abs_neg, abs_of_nonneg (r_nonneg y)]; exact r_le_half hy

end Hyp
end GreenFD
end Complex
end
end P2MW.S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt
