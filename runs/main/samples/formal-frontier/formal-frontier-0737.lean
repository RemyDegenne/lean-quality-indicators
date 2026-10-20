@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem primewisePadicClosedAddSubgroupOfExponents_top_toAddSubgroup :
    (primewisePadicClosedAddSubgroupOfExponents.{u} ⊤).toAddSubgroup = ⊥ := by
  change (primewisePadicIdealOfExponents ⊤).toAddSubgroup = ⊥
  rw [primewisePadicIdealOfExponents_top]
  rfl

end ProfiniteGrp
end
