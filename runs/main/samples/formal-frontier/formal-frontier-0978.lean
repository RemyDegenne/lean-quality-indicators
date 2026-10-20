@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem liftedPadicQuotientContinuousAddEquivZMod_apply
    (p : Nat.Primes) (n : ℕ)
    (x : ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p (n : ℕ∞)) :
    liftedPadicQuotientContinuousAddEquivZMod p n x =
      liftedPadicQuotientRingEquivZMod p n x :=
  rfl

end ProfiniteGrp
end
