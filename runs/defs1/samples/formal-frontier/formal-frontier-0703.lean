@[expose] public section

open Set

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The coordinatewise exponents of an ideal in the primewise p-adic ring. -/
noncomputable def primewisePadicIdealExponents
    (I : Ideal primewisePadicRing.{u}) (p : Nat.Primes) : ℕ∞ :=
  liftedPadicIdealExponent p
    (I.map (Pi.evalRingHom
      (fun q : Nat.Primes ↦ ULift.{u} ℤ_[q.1]) p))

end ProfiniteGrp
end
