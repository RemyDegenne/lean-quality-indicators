@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The infinite-exponent quotient is continuously additively equivalent to
the uplifted p-adic factor. -/
noncomputable def liftedPadicQuotientContinuousAddEquivTop
    (p : Nat.Primes) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) ≃ₜ+
      ULift.{u} ℤ_[p.1] :=
  ContinuousAddEquiv.mk (liftedPadicQuotientRingEquivTop p).toAddEquiv
    (by
      rw [← (QuotientRing.isOpenQuotientMap_mk
        (liftedPadicIdealOfExponent p ⊤)).continuous_comp_iff]
      change Continuous (id : ULift.{u} ℤ_[p.1] → ULift.{u} ℤ_[p.1])
      exact continuous_id)
    (by
      change Continuous (Ideal.Quotient.mk
        (liftedPadicIdealOfExponent p ⊤))
      exact (QuotientRing.isOpenQuotientMap_mk _).continuous)

end ProfiniteGrp
end
