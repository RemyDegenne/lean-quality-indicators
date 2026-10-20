@[expose] public section

universe u v

namespace ProfiniteGrp

open scoped IsDomain

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padicQuotientFactor_isAddTorsionFree_iff (p : Nat.Primes) (e : ℕ∞) :
    IsAddTorsionFree (padicQuotientFactor.{u} p e) ↔ e = 0 ∨ e = ⊤ := by
  refine ENat.recTopCoe ?_ (fun n ↦ ?_) e
  · change IsAddTorsionFree (padicQuotientFactorTop.{u} p) ↔ _
    simp [padicQuotientFactorTop_isAddTorsionFree]
  · by_cases hn : n = 0
    · subst n
      change IsAddTorsionFree (padicQuotientFactorNat.{u} p 0) ↔ _
      simp [padicQuotientFactorNat_zero_isAddTorsionFree]
    · change IsAddTorsionFree (padicQuotientFactorNat.{u} p n) ↔ _
      constructor
      · intro h
        exact False.elim ((padicQuotientFactorNat_not_isAddTorsionFree p n hn) h)
      · intro h
        simp [hn] at h

end ProfiniteGrp
end
