namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology BigOperators NNReal BoundedContinuousFunction

namespace SphericalPerceptronFreeEnergy

lemma cappedAError_tendsto (μ : ℕ→ProbabilityMeasure Time) (ν : ProbabilityMeasure Time)
    (hμ : Tendsto μ atTop (𝓝 ν)) {B : ℝ} (hB : B<1) :
    Tendsto (fun j=>cappedAError (μ j) ν B) atTop (𝓝 0) := by
  have hd (t : ℝ) : Tendsto (fun j=>cappedDensity (μ j) B t) atTop (𝓝 (cappedDensity ν B t)) := by
    exact ((tendsto_const_nhds.max (realTail_weak_tendsto μ ν hμ t)).inv₀
      (ne_of_gt ((sub_pos.mpr hB).trans_le (le_max_left _ _)))).pow 2
  have hh:=tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Ioc (0:ℝ) 1))
    (fun _ : ℝ=>2*(1-B)⁻¹^2)
    (F:=fun j t=>|cappedDensity (μ j) B t-cappedDensity ν B t|)
    (f:=fun _=>0)
    (fun j=>((cappedDensity_continuous (μ j) hB).sub (cappedDensity_continuous ν hB)).abs.measurable.aestronglyMeasurable)
    (integrable_const _) (fun j=>ae_of_all _ fun t=>by
      have h₁:=cappedDensity_bound (μ j) hB t
      have h₂:=cappedDensity_bound ν hB t
      rw [Real.norm_eq_abs,abs_abs]
      exact abs_le.mpr ⟨by linarith,by linarith⟩)
    (ae_of_all _ fun t=>by simpa using ((hd t).sub (tendsto_const_nhds (x:=cappedDensity ν B t))).abs)
  simpa only [cappedAError,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_zero] using hh

end SphericalPerceptronFreeEnergy
end
end OAI
