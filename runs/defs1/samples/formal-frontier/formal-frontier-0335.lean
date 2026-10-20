@[expose] public section

universe u v w

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Change only the `ULift` universe of a p-adic factor. -/
noncomputable def liftedPadicChangeUniverseRingEquiv (p : Nat.Primes) :
    ULift.{u} ℤ_[p.1] ≃+* ULift.{v} ℤ_[p.1] :=
  ULift.ringEquiv.trans ULift.ringEquiv.symm

end ProfiniteGrp
end
