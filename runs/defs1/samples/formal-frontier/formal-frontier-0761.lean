@[expose] public section

open Set

universe u

namespace Order.Ideal

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

/-- The principal-ideal embedding as a bounded lattice homomorphism. -/
def principalHom : BoundedLatticeHom A (Ideal A) where
  toFun := principal
  map_sup' a b := by
    apply Ideal.ext
    ext x
    constructor
    · intro hx
      exact ⟨a, mem_principal_self, b, mem_principal_self, hx⟩
    · rintro ⟨i, hi, j, hj, hx⟩
      exact hx.trans (sup_le_sup hi hj)
  map_inf' a b := by
    apply Ideal.ext
    ext x
    exact le_inf_iff
  map_top' := principal_top
  map_bot' := principal_bot

end Order.Ideal
end
