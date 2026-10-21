namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal

open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionFamily

open Directions DirectionInterpolation DirectionAsymptotics GaussianTools FiniteNets

open MeasureTheory ProbabilityTheory Set Filter

open scoped BigOperators Topology

variable {m N S : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

lemma good_chart_interpolation {N S : ℕ} (g : Fin S → Fin N → E)
    (hg : ∀ s, g s ∉ normBad) {v v' : E} {ρ q q' : ℝ}
    (hd : ‖v-v'‖ ≤ ρ) (hq : q+2*Real.sqrt m*ρ ≤ q') :
    badCount (projectionBad q' v) g ≤ badCount (projectionBad q v') g := by
  apply badCount_le_of_imp g
  intro s hs
  by_contra hn
  obtain ⟨i,hi⟩ := hs
  have hp : |inner ℝ v' (g s i)| ≤ q := by
    by_contra h; exact hn ⟨i,lt_of_not_ge h⟩
  have hgn : ‖g s i‖ ≤ 2*Real.sqrt m := by
    have := (normBounds_of_not_bad (hg s) i).2
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m), Real.sqrt_nonneg (m : ℝ), norm_nonneg (g s i)]
  have hh := (projection_interpolate hgn (by positivity) hd hp).trans hq
  exact not_lt_of_ge hh hi

end UniformSparsestCut.DirectionFamily
end
end OAI
