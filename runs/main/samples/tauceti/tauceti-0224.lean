public section

open Complex Filter Function Module Set Topology

open scoped ComplexConjugate ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
  [ChartedSpace E M] {f : M → ℝ} {x : M}

section Positivity

theorem IsManifoldStrictlyPlurisubharmonicAt.isManifoldStronglyPseudoconvexAt
    [FiniteDimensional ℂ E] (h : IsManifoldStrictlyPlurisubharmonicAt E f x) (q : ℕ) :
    IsManifoldStronglyPseudoconvexAt E q f x :=
  IsStrictlyPlurisubharmonicAt.isStronglyPseudoconvexAt h q

end Positivity
end TauCeti
end
end
