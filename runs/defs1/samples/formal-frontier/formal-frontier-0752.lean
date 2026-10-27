@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The integral unit in the multiplicative p-adic factor. -/
noncomputable def padicFactorGenerator (p : Nat.Primes) : padicFactor.{u} p :=
  Multiplicative.ofAdd (ULift.up (1 : ℤ_[p.1]))

end ProfiniteGrp
end
