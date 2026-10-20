public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set

open scoped ENNReal Real

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

theorem exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top
    (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤) {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, circleImageLength f (ball c r) ζ ρ ≠ ⊤ ∧
      diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε ∧
      IsBounded (f '' (ball c r ∩ sphere ζ ρ)) := by
  obtain ⟨ρ, hρmem, hlen⟩ :=
    exists_circleImageLength_lt_of_lintegral_ne_top (s := ball c r) f measurableSet_ball ζ hfin
      (ENNReal.ofReal_pos.mpr hε).ne' hR
  have hfin' : circleImageLength f (ball c r) ζ ρ ≠ ⊤ := (hlen.trans ENNReal.ofReal_lt_top).ne
  exact ⟨ρ, hρmem, hfin', diam_image_ball_inter_sphere_le hf hε.le hlen.le,
    isBounded_image_ball_inter_sphere_of_circleImageLength_ne_top hf hfin'⟩

end TauCeti
end
