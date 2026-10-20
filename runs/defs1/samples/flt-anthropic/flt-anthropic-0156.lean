namespace P2MW.S_ExtCitation_LocalLevel_exists_common_overlayer

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory groupCohomology ExtCitation.LocalLevel

set_option maxHeartbeats 800000

namespace OVbProof

noncomputable section

open Polynomial

variable (q : ℕ) [Fact q.Prime]

section Layer

variable (K : IntermediateField ℚ_[q] (PadicAlgCl q))
  (L : IntermediateField ℚ_[q] (PadicAlgCl q))
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (hKL : K ≤ L) (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)

variable (D : Subgroup (Gw q K)) [D.Normal] (hD : D ≤ (Gw q L).subgroupOf (Gw q K))

def NSub : Subgroup (Gw q K ⧸ D) := ((Gw q L).subgroupOf (Gw q K)).map (QuotientGroup.mk' D)

end Layer
end
end OVbProof
end P2MW.S_ExtCitation_LocalLevel_exists_common_overlayer
