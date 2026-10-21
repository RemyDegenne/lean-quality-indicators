namespace OAI

open Set Filter MeasureTheory

open scoped ENNReal

open Set Filter MeasureTheory

open scoped ENNReal

open Set MeasureTheory ProbabilityTheory

open scoped Classical BigOperators ENNReal

open Set Filter MeasureTheory

open scoped ENNReal

open Set MeasureTheory ProbabilityTheory

open scoped Classical BigOperators ENNReal

open Set Filter MeasureTheory

open scoped ENNReal

open Set MeasureTheory ProbabilityTheory

open scoped Classical BigOperators ENNReal

open Set Filter MeasureTheory

open scoped ENNReal Topology

open Set Filter MeasureTheory

open scoped ENNReal Topology

open scoped Classical BigOperators

open scoped Classical BigOperators

open scoped BigOperators Classical

open scoped Classical BigOperators

open scoped Classical BigOperators

open scoped BigOperators Classical

open Set Filter MeasureTheory

open scoped ENNReal

open Set MeasureTheory ProbabilityTheory

open scoped Classical BigOperators ENNReal

namespace CylinderAngle

open Set MeasureTheory Metric InnerProductGeometry CylinderVolume ConeStretch

open scoped ENNReal

lemma projective_perp_bound {n : ℕ} (u x : Space n) (hu : ‖u‖ = 1) (hx : x ≠ 0)
    {L ξ : ℝ} (hL : 0 ≤ L) (hξ : 0 ≤ ξ) (hxL : ‖x‖ ≤ L)
    (hang : ProjectiveCaps.angle u x ≤ ξ) :
    ‖x‖^2-(inner ℝ u x)^2 ≤ (L*ξ)^2 := by
  rcases (min_le_iff.mp hang) with h | h
  · exact ordinary_perp_bound u x hu hx hL hξ hxL h
  · simpa only [norm_neg,inner_neg_right,neg_sq] using
      ordinary_perp_bound u (-x) hu (neg_ne_zero.mpr hx) hL hξ
        (by simpa only [norm_neg] using hxL) h

end CylinderAngle
end OAI
