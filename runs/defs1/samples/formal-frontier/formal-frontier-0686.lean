@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The coordinatewise exponents of a closed additive subgroup of the
primewise p-adic ring. -/
noncomputable def primewisePadicClosedAddSubgroupExponents
    (K : ClosedAddSubgroup primewisePadicRing.{u}) : Nat.Primes → ℕ∞ :=
  primewisePadicIdealExponents (primewisePadicClosedAddSubgroupIdeal K)

end ProfiniteGrp
end
