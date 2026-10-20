public section

open Set

attribute [local instance] Classical.decEq

open AbstractSimplicialComplex

namespace TauCeti

variable {ι : Type*}

@[simp]
theorem mem_standardGeometricComplex_space_iff {K : AbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (standardGeometricComplex K).space ↔
      (∀ i, 0 ≤ x i) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ∈ K :=
  Geometry.SimplicialComplex.mem_space_onFinsupp_iff (K := K.toPreAbstractSimplicialComplex)

end TauCeti
end
