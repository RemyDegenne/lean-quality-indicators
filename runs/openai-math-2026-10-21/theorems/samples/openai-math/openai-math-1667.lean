namespace OAI

namespace TwoPointCorrelations

open Finset

open scoped Classical

theorem minor_arc_typical_parameter_range_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I : Set ι) P →
      ∀ i ∈ I, ∀ (X H : ℕ), 2 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → 1 ≤ Real.log (Real.log (H : ℝ)) →
      ∀ W : ℝ, 1 ≤ W →
      (∀ p ∈ P i, p ≠ 2 ∧ 2 * R₀ ≤ p ∧
        2 * W ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (H : ℝ) / W) →
      ∀ (F : ℕ → ℂ), Multiplicative F → OneBounded F →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      W ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C * (X : ℝ) * H * Real.log (Real.log (H : ℝ)) * (Real.log (H : ℝ)/W)^(1/4:ℝ) +
          3 * (H : ℝ) * (X + H) * ∑ p ∈ P i, 1 / (p : ℝ) ^ 2 := by
  obtain ⟨C, hC, R₀, hbound⟩ := minor_arc_typical_parameter_saving
  refine ⟨3 * C, by positivity, R₀, ?_⟩
  intro ι I P hP hdis i hi X H hH hHX hlogH hloglog W hW hrange F hF hFb
    r q hq hWq hqH α hcop happ
  obtain ⟨hJ, hPJ, hR, hgeom⟩ := minor_arc_parameter_range_dyadics (P i) H R₀ (hP i hi)
    W hW (fun p hp => (hrange p hp).2)
  have hbound' := hbound I P hP hdis i hi ((P i).image (Nat.log 2)) X H (Nat.log 2 H)
    (by omega) hHX hlogH hJ hPJ (fun p hp => (hrange p hp).1)
    (fun j hj => ⟨(hR j hj).1, (hR j hj).2.trans hHX⟩) W hW hgeom
    F hF hFb r q hq hWq hqH α hcop happ
  apply hbound'.trans
  apply add_le_add _ le_rfl
  have hh := mul_le_mul_of_nonneg_left (minor_arc_dyadic_log_log_bound H hH hlogH hloglog)
    (by positivity : 0 ≤ C * (X : ℝ) * H)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (show 0 ≤ Real.log (H:ℝ)/W by positivity) (1/4:ℝ))
  convert hh' using 1
  ring

end TwoPointCorrelations
end OAI
