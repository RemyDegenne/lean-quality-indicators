namespace P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

attribute [-instance] Quotient.instLE_mathlib

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_DenominatorClearing

namespace M4aLocalCFT

universe u

open AddSubgroup

variable {A B V : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]

p2m_reactivate

section Gates

theorem intCast_intertwines_norm :
    ∀ b, ratDiagPair.norm (intCastHom₂ b) = intCastHom₂ (intDiagPair.norm b) := by
  intro p
  show ((2 * (p.1 : ℚ)), (0 : ℚ)) = (((2 * p.1 : ℤ) : ℚ), ((0 : ℤ) : ℚ))
  rw [Prod.mk.injEq]
  push_cast
  exact ⟨by ring, by ring⟩

end Gates
end M4aLocalCFT
end Fold_DenominatorClearing
end P2MW.S_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank
