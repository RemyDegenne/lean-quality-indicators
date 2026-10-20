public section

open scoped LinearAlgebra.Projectivization

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

namespace Projectivization

@[simp]
theorem dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v := by
  rw [dependent_iff_not_independent, independent_iff, linearIndependent_fin2]
  dsimp only [Function.comp_def, Matrix.cons_val]
  simp only [not_and, not_forall, not_not, ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v),
    mk_rep, Classical.imp_iff_right_iff]
  exact Or.inl (rep_nonzero v)

end Projectivization
end
