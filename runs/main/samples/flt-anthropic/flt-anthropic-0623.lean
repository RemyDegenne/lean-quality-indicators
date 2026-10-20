namespace P2MW.S_M4aHerbrand_sUnitQuot_fixedRank_eq

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

p2m_reactivate

p2m_reactivate

section Fold_IdempotentCycleShapiro

set_option autoImplicit false

namespace M4aHerbrand

namespace IdempotentCycle

p2m_open

open M4aLocalCFT M4aLocalCFT.HerbrandPair M4aLocalCFT.SemilocalHerbrand M4aLocalCFT.LocalUnitsCohomology

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Units

variable {C : Type*} [CommRing C] {d : ℕ} [NeZero d]

variable (σ : C ≃+* C) (e : ZMod d → C) (he : CompleteOrthogonalIdempotents e) (hσe : ∀ i, σ (e i) = e (i + 1))

theorem unitsSplitting_toMul_val (a : Additive Cˣ) (i : ZMod d) :
    (((unitsSplitting σ e he hσe a i).toMul : (Corner e he)ˣ) : Corner e he) = splittingHom σ e he (a.toMul : C) i := rfl

end Units
end IdempotentCycle
end M4aHerbrand
end Fold_IdempotentCycleShapiro
end P2MW.S_M4aHerbrand_sUnitQuot_fixedRank_eq
