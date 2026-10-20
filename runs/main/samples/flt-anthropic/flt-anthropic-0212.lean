namespace P2MW.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter

open TensorProduct AutomorphicForm

open scoped TensorProduct.RightActions

noncomputable section

namespace TwistedUnipotentTermK6b

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Unipotent

variable (K L) (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalUnipotent_mem_semiLocalIntegralSet {u : SL K L v} (hu : u ∈ semiLocalIntegers K L v) :
    TwistedUnipotentTerm.semiLocalUnipotent K L v u ∈ semiLocalIntegralSet K L v := by
  have h0 := zero_mem_semiLocalIntegers K L v
  have h1 := one_mem_semiLocalIntegers K L v
  have hn : -u ∈ semiLocalIntegers K L v := by
    rw [← mem_semiLocalSubring_iff] at hu ⊢
    exact Subring.neg_mem _ hu
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_semiLocalUnipotent]
    fin_cases i <;> fin_cases j <;> simp [h0, h1, hu]
  · rw [coe_inv_semiLocalUnipotent]
    fin_cases i <;> fin_cases j <;> simp [h0, h1, hn]

end Unipotent
end TwistedUnipotentTermK6b
end
end P2MW.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport
