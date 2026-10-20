@[expose] public section

open Set

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The ideal in an uplifted p-adic factor having the prescribed exponent. -/
noncomputable def liftedPadicIdealOfExponent (p : Nat.Primes) (n : ℕ∞) :
    Ideal (ULift.{u} ℤ_[p.1]) :=
  (liftedPadicIdealOrderIso p).symm (OrderDual.toDual n)

end ProfiniteGrp
end
