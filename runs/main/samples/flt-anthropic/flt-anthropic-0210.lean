namespace P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

attribute [-instance] Quotient.instLE_mathlib

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_IdempotentCycleShapiro

set_option autoImplicit false

namespace M4aHerbrand

namespace IdempotentCycle

p2m_open

open M4aLocalCFT M4aLocalCFT.HerbrandPair M4aLocalCFT.SemilocalHerbrand M4aLocalCFT.LocalUnitsCohomology

p2m_reactivate

section Cycle

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]

variable (σ : C ≃+* C) (e : ZMod d → C) (hσe : ∀ i, σ (e i) = e (i + 1))

omit [NeZero d] in
include hσe in
theorem pow_apply_e (k : ℕ) (i : ZMod d) : (σ ^ k) (e i) = e (i + k) := by
  induction k generalizing i with
  | zero => rw [pow_zero, RingAut.one_apply, Nat.cast_zero, add_zero]
  | succ k ih => rw [pow_succ, RingAut.mul_apply, hσe, ih, Nat.cast_succ, add_assoc, add_comm 1]

end Cycle
end IdempotentCycle
end M4aHerbrand
end Fold_IdempotentCycleShapiro
end P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
