public section

noncomputable section

open Finset Set TauCeti TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

namespace BarycentricSubdivision

/-- The point of the barycentric subdivision determined by a face, an ordering of its vertices,
and a decreasing sequence of barycentric coordinates. -/
noncomputable def orderedSubdivisionPoint {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) (hc : ∀ {k}, k < σ.1.card → c (k + 1) ≤ c k)
    (hsum : ∑ k ∈ Finset.range σ.1.card, c k = 1) (hcard : c σ.1.card = 0) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  faceInclusion _ (orderedSubdivisionFace σ e)
    (orderedStandardSimplex σ e c hc hsum hcard)

end BarycentricSubdivision
end AbstractSimplicialComplex
end
end
