@[expose] public section

open Set

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem liftedPadicIdealOfExponent_zero (p : Nat.Primes) :
    liftedPadicIdealOfExponent p 0 = ⊤ := by
  simpa using liftedPadicIdealOfExponent_natCast p 0

end ProfiniteGrp
end
