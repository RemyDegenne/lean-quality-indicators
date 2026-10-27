public section

namespace TauCeti

namespace RamificationIndex

/-- The quotient `m / n` attached to a divisibility relation `n ≤ m`. -/
def transitionDegree {n m : RamificationIndex} (_h : n ≤ m) : ℕ+ :=
  PNat.divExact m.toPNat n.toPNat

end RamificationIndex
end TauCeti
end
