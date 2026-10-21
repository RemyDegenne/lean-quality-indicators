namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

open scoped Simplicial

namespace Problem340.SingularAcyclicModels

lemma model_exact (n k : ℕ) : (singularFunctor.obj (model n)).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact realSingularHomology_subsingleton_of_contractible (k + 1) (by omega) (model n)

end Problem340.SingularAcyclicModels
end
end OAI
