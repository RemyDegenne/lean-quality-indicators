namespace P2MW.S_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory groupCohomology ExtCitation.LocalLevel

set_option maxHeartbeats 800000

namespace AUXProof

variable (q : ℕ) [Fact q.Prime]

variable (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]

noncomputable section

open Polynomial

section Layer

variable (K : IntermediateField ℚ_[q] (PadicAlgCl q))
  (L : IntermediateField ℚ_[q] (PadicAlgCl q))
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (hKL : K ≤ L) (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)

noncomputable def rHom : Gw q K →* G where
  toFun σ := Classical.choose (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2))
  map_one' := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [Classical.choose_spec (exists_restrict q K L G hK (1 : Gw q K) ((IntermediateField.mem_fixingSubgroup_iff K _).1 (1 : Gw q K).2)) x, one_smul]
    rfl
  map_mul' σ τ := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    apply Subtype.ext
    rw [Classical.choose_spec (exists_restrict q K L G hK (σ * τ) ((IntermediateField.mem_fixingSubgroup_iff K _).1 (σ * τ).2)) x, mul_smul,
      Classical.choose_spec (exists_restrict q K L G hK σ ((IntermediateField.mem_fixingSubgroup_iff K _).1 σ.2)),
      Classical.choose_spec (exists_restrict q K L G hK τ ((IntermediateField.mem_fixingSubgroup_iff K _).1 τ.2))]
    rfl

end Layer
end
end AUXProof
end P2MW.S_ExtCitation_LocalLevel_exists_frobenius_uniformiser_inf_level
