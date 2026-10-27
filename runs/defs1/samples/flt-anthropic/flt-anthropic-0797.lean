namespace P2MW.S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open

namespace ExtCitation

namespace LocalLevel

namespace Ws25UU

p2m_open

open IsLocalRing

section Layer

variable {q : ℕ} [Fact q.Prime]

variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}

variable {G : Type} [Group G] [MulSemiringAction G L]

noncomputable def autOf (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) :
    L ≃ₐ[ℚ_[q]] L :=
  { MulSemiringAction.toRingEquiv G L g with
    commutes' := fun x => hG g x }

end Layer
end Ws25UU
end LocalLevel
end ExtCitation
end P2MW.S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq
