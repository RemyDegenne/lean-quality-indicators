@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The additive coordinate exponents of a closed subgroup of
`primewisePadic`. -/
noncomputable def primewisePadicClosedSubgroupExponents
    (H : ClosedSubgroup primewisePadic.{u}) : Nat.Primes → ℕ∞ :=
  primewisePadicClosedAddSubgroupExponents
    (primewisePadicClosedSubgroupToClosedAddSubgroup H)

end ProfiniteGrp
end
