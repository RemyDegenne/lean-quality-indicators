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

section Fold_SemilocalHerbrand

open Finset

namespace M4aLocalCFT

open HerbrandPair LocalUnitsCohomology

namespace SemilocalHerbrand

variable (d m : ℕ) {M : Type*} [AddCommGroup M] (τ : AddAut M)

variable [NeZero d]

p2m_reactivate

p2m_reactivate

section Gates

theorem coinducedPair_not_isCohTrivial :
    ¬ IsCohTrivial (coinducedPair 2 2 (1 : AddAut ℤ) (one_pow 2)) := by
  intro h
  have h2 := tateCard₀_coinducedPair_int 2 2 (by omega)
  rw [h.1] at h2
  omega

end Gates
end SemilocalHerbrand
end M4aLocalCFT
end Fold_SemilocalHerbrand
end P2MW.S_M4aHerbrand_sUnitQuot_fixedRank_eq
