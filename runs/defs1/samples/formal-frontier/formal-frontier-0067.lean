@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- At a finite exponent, identify the factor with the corresponding
uplifted residue ring. This also works at exponent zero. -/
noncomputable def padicQuotientFactorContinuousAddEquivFinite
    (p : Nat.Primes) (exponent : ℕ∞) (hfinite : exponent < ⊤) :
    padicQuotientFactor.{u} p exponent ≃ₜ+
      ULift.{u} (ZMod (p.1 ^ exponent.toNat)) := by
  refine ENat.recTopCoe (C := fun n ↦ n < ⊤ →
      padicQuotientFactor.{u} p n ≃ₜ+ ULift.{u} (ZMod (p.1 ^ n.toNat)))
      ?_ ?_ exponent hfinite
  · intro htop
    exact ((lt_irrefl (⊤ : ℕ∞)) htop).elim
  · intro n _
    change ULift.{u} (ZMod (p.1 ^ n)) ≃ₜ+ ULift.{u} (ZMod (p.1 ^ n))
    exact ContinuousAddEquiv.refl _

end ProfiniteGrp
end
