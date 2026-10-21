namespace OAI

namespace PlanarFPP

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actualSourceTimeConstant_lattice_limits (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ z : Vertex,
      Tendsto (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z)/n) atTop
        (𝓝 (actualSourceTimeConstant (latticeEmbed z))) := by
  have hm : MeasurePreserving (fun ω => companionWeights (fun e => τ e ω)) P
      CompanionFPP.environmentLaw := ⟨measurable_companionWeights h.measurable,h.companionLaw⟩
  filter_upwards [hm.quasiMeasurePreserving.ae CompanionFPP.actualTimeNorm_hasTimeConstant] with ω hω
  intro z
  have hz := hω z
  simp only [companion_passageTime_eq] at hz
  have he (n : ℕ) : CompanionFPP.scaleVertex n z = n • z := by
    ext <;> simp [CompanionFPP.scaleVertex,nsmul_eq_mul]
  simp only [he] at hz
  exact hz

end PlanarFPP
end OAI
