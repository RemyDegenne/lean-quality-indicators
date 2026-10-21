namespace OAI

noncomputable section

namespace Kaplansky

section

open CategoryTheory Limits AlgebraicTopology Simplicial Convexity

theorem simplexCombination_reindex {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (v : κ → StdSimplex ℝ μ) (f : ι → κ) (t : StdSimplex ℝ ι) :
    simplexCombination (v ∘ f) t = simplexCombination v (StdSimplex.map f t) := by
  exact (Convexity.iConvexComb_map t f v).symm

end
end Kaplansky
end
end OAI
