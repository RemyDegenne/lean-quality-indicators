namespace OAI

noncomputable section

open MeasureTheory

open scoped BoundedContinuousFunction

open MeasureTheory FourierTransform

open scoped BoundedContinuousFunction RealInnerProductSpace ENNReal

namespace TamingCompatibility.FourierCutoff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma modulate_coe (g : Lp ℂ 2 (volume : Measure E)) (x : E) :
    modulate g x =ᵐ[volume] fun ξ => (Real.fourierChar ⟪ξ,x⟫ : ℂ) * g ξ := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (((phase x).memLp_top (μ := volume)).toLp _) g,
    ((phase x).memLp_top (μ := volume)).coeFn_toLp] with ξ h1 h2
  change modulate g x ξ = (((phase x).memLp_top (μ := volume)).toLp _) ξ * g ξ at h1
  rw [h1, h2]
  rfl

end TamingCompatibility.FourierCutoff
end
end OAI
