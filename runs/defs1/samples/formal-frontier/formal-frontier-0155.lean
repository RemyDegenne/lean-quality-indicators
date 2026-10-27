@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The infinite-exponent quotient ring is the uplifted p-adic ring itself. -/
noncomputable def liftedPadicQuotientRingEquivTop (p : Nat.Primes) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) ≃+*
      ULift.{u} ℤ_[p.1] :=
  (Ideal.quotEquivOfEq (liftedPadicIdealOfExponent_top p)).trans
    (RingEquiv.quotientBot _)

end ProfiniteGrp
end
