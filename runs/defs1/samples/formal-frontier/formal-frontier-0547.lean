@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The finite residue-ring equivalence as a continuous additive equivalence. -/
noncomputable def liftedPadicQuotientContinuousAddEquivZMod
    (p : Nat.Primes) (n : ℕ) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p (n : ℕ∞)) ≃ₜ+
      ZMod (p.1 ^ n) := by
  letI := discreteTopology_liftedPadicQuotient_natCast.{u} p n
  exact ContinuousAddEquiv.mk
    (liftedPadicQuotientRingEquivZMod p n).toAddEquiv
      continuous_of_discreteTopology continuous_of_discreteTopology

end ProfiniteGrp
end
