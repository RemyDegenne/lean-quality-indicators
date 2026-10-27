@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- A quotient factor is continuously additively equivalent to its
universe-uniform finite-or-infinite model. -/
noncomputable def liftedPadicQuotientContinuousAddEquivFactor
    (p : Nat.Primes) (e : ℕ∞) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p e) ≃ₜ+
      padicQuotientFactor p e := by
  refine ENat.recTopCoe ?_ (fun n ↦ ?_) e
  · change (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) ≃ₜ+
      ULift.{u} ℤ_[p.1]
    exact liftedPadicQuotientContinuousAddEquivTop.{u} p
  · change (ULift.{u} ℤ_[p.1] ⧸
        liftedPadicIdealOfExponent p (n : ℕ∞)) ≃ₜ+
      ULift.{u} (ZMod (p.1 ^ n))
    exact (liftedPadicQuotientContinuousAddEquivZMod.{u} p n).trans
      (zmodContinuousAddEquivULift.{u} p n)

end ProfiniteGrp
end
