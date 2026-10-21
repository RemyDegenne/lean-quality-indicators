namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology NNReal ENNReal BigOperators

namespace SKValue

lemma IsMinimizer.contactPotential_ae_zero {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {T : ℝ} (hT : T∈Ico (0 : ℝ) 1) :
    ∀ᵐ s ∂γ.truncatedMass T hT,contactPotential W γ X s=0 := by
  have hh := hγ.variation_inequality hX (γ.removeBelow (γ.coeff T))
  simp_rw [γ.removeBelow_sub,neg_mul] at hh
  rw [intervalIntegral.integral_neg] at hh
  obtain ⟨hi,he⟩ := hX.contact_fubini hT
  have hnn : 0≤ᵐ[γ.truncatedMass T hT] contactPotential W γ X := by
    filter_upwards [γ.truncatedMass_ae_mem hT] with s hs
    exact hγ.contactPotential_nonneg hX ⟨hs.1,hs.2.trans hT.2.le⟩
  apply (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp
  have hpos := integral_nonneg_of_ae hnn
  rw [he] at hpos ⊢
  linarith

end SKValue
end
end OAI
