@[expose] public section

open CategoryTheory Function Set

open CategoryTheory.Limits

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The additive group of `p`-adic integers, written multiplicatively as a
profinite group in an arbitrary universe. -/
noncomputable def padicFactor (p : Nat.Primes) : ProfiniteGrp.{u} := by
  letI : CompactSpace (ULift.{u} ℤ_[p.1]) :=
    Homeomorph.compactSpace (Homeomorph.ulift (X := ℤ_[p.1])).symm
  letI : TotallyDisconnectedSpace (ULift.{u} ℤ_[p.1]) :=
    Homeomorph.totallyDisconnectedSpace (Homeomorph.ulift (X := ℤ_[p.1])).symm
  exact ProfiniteGrp.of (Multiplicative (ULift.{u} ℤ_[p.1]))

end ProfiniteGrp
end
