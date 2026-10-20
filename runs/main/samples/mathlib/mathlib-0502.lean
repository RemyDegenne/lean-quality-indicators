@[expose] public section

open Module Filter

open scoped Topology Nat

noncomputable section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)

namespace PeriodPair

lemma ω₂_div_two_notMem_lattice : L.ω₂ / 2 ∉ L.lattice := by
  simpa [inv_mul_eq_div] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1 / 2)).not.mpr (by simp)

end PeriodPair
end
end
