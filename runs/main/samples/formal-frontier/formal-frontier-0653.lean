@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem primewisePadicClosedAddSubgroupOfExponents_injective :
    Function.Injective
      (primewisePadicClosedAddSubgroupOfExponents.{u} :
        (Nat.Primes → ℕ∞) → ClosedAddSubgroup primewisePadicRing.{u}) := by
  intro e d h
  simpa using congrArg primewisePadicClosedAddSubgroupExponents h

end ProfiniteGrp
end
