@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem primewisePadicClosedAddSubgroupOfExponents_zero_toAddSubgroup :
    (primewisePadicClosedAddSubgroupOfExponents.{u} 0).toAddSubgroup = ⊤ := by
  change (primewisePadicIdealOfExponents 0).toAddSubgroup = ⊤
  rw [primewisePadicIdealOfExponents_zero]
  rfl

end ProfiniteGrp
end
