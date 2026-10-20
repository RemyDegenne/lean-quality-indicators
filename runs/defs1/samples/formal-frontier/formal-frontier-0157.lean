@[expose] public section

open Set

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Ideals in an uplifted p-adic factor, ordered by inclusion, correspond to
extended natural exponents in the reverse order.

Uses Mathlib’s p-adic ideal order and `ULift` transport; this factor classification is not
attributed to a printed procyclic theorem. -/
noncomputable def liftedPadicIdealOrderIso (p : Nat.Primes) :
    Ideal (ULift.{u} ℤ_[p.1]) ≃o ℕ∞ᵒᵈ :=
  ULift.ringEquiv.idealComapOrderIso.symm.trans
    (IsDiscreteValuationRing.idealOrderIsoENat ℤ_[p.1])

end ProfiniteGrp
end
