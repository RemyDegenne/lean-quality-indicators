public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

open scoped commutatorElement

section Field

variable {Γ : Type*} [Field Γ] (σ : Γ ≃+* Γ)

variable {σ}

variable (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ

theorem trace_mem_fixedSubfield (c : Γ) : c + σ c + σ (σ c) ∈ fixedSubfield σ := by
  rw [mem_fixedSubfield, map_add, map_add, hσ]
  ring

end Field
end CFSG.LocalAnalysis.EvenBN.TrialityD4
end
