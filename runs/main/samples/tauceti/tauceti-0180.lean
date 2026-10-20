public section

noncomputable section

open Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {K L : AbstractSimplicialComplex ι}

theorem support_faceInclusion_mem {P : PreAbstractSimplicialComplex ι}
    (hP : P ≤ L.toPreAbstractSimplicialComplex) {σ : Finset ι} (hσ : σ ∈ P)
    (x : StandardSimplex σ) : (faceInclusion L ⟨σ, hP hσ⟩ x).1.support ∈ P := by
  rw [faceInclusion_val]
  exact P.isRelLowerSet_faces.mem_of_le hσ (StandardSimplex.support_subset x)
    (by simpa only [faceInclusion_val] using
      L.isRelLowerSet_faces.prop_of_mem (support_mem L (faceInclusion L ⟨σ, hP hσ⟩ x)))

end AbstractSimplicialComplex
end
end
