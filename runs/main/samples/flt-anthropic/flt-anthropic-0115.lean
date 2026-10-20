namespace P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed

set_option autoImplicit false

namespace ChevalleyHom

variable {L Ω : Type*} [Field L] [Field Ω]

section Maximal

variable {Γ₀ Γ : Subring (L × Ω)} (hmax : Maximal (· ∈ Above Γ₀) Γ)

include hmax

theorem mem_maximalIdeal_iff (x : IsGraph.dom Γ) :
    haveI := isLocalRing hmax
    x ∈ IsLocalRing.maximalIdeal (IsGraph.dom Γ) ↔ (isGraph_of_maximal hmax).hom x = 0 := by
  haveI := isLocalRing hmax
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff hmax, not_not]

end Maximal
end ChevalleyHom
end P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed
