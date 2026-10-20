public section

namespace ValueDistribution

open Asymptotics Filter Function.locallyFinsuppWithin MeromorphicOn Metric Real

section SecondPart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a₀ : E} {f : ℂ → E}

theorem abs_characteristic_sub_characteristic_shift_le {r : ℝ} (h : Meromorphic f) :
    |characteristic f ⊤ r - characteristic (f · - a₀) ⊤ r| ≤ log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x ↦ log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x ↦ log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    fun_prop
  rw [← Pi.sub_apply, characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity_top, Pi.sub_apply, ← circleAverage_sub h₁f h₂f]
  apply le_trans abs_circleAverage_le_circleAverage_abs
  apply circleAverage_mono_on_of_le_circle
  · apply (h₁f.sub h₂f).abs
  · intro θ hθ
    simp only [Pi.abs_apply, Pi.sub_apply]
    by_cases h : 0 ≤ log⁺ ‖f θ‖ - log⁺ ‖f θ - a₀‖
    · simpa [abs_of_nonneg h, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
        using (posLog_norm_add_le (f θ - a₀) a₀)
    · simp only [abs_of_nonpos (le_of_not_ge h), neg_sub, tsub_le_iff_right,
        add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      convert posLog_norm_add_le (-f θ) a₀ using 2
      · rw [← norm_neg]
        abel_nf
      · simp

end SecondPart
end ValueDistribution
end
