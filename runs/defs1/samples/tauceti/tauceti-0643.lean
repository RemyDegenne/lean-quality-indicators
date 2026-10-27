public section

open CategoryTheory

namespace TauCeti

/-- The Young permutation module of the coarsest partition `(n)` is the trivial representation:
there is only one `(n)`-tabloid. -/
noncomputable def permutationModuleIndiscreteIsoTrivial (n : ℕ) :
    permutationModule (Nat.Partition.indiscrete n) ≅
      Rep.trivial ℚ (Equiv.Perm (Fin n)) ℚ :=
  quotientIsoCongr ℚ (youngSubgroup_indiscrete n) ≪≫ quotientTopIsoTrivial ℚ

end TauCeti
end
