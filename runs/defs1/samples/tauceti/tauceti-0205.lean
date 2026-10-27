public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

variable {K Ω}

section Normal

variable [Normal K Ω]

variable (K Ω) in
/-- **The Galois group of the maximal abelian extension is the topological abelianization**: for
`Ω/K` normal, restriction to `K^{ab}` induces an isomorphism of topological groups
`Gal(Ω/K) ⧸ closure [Gal(Ω/K), Gal(Ω/K)] ≃ₜ* Gal(K^{ab}/K)`. -/
def topologicalAbelianizationEquivMaximalAbelianExtension :
    TopologicalAbelianization Gal(Ω/K) ≃ₜ* Gal(maximalAbelianExtension K Ω/K) :=
  ((ContinuousMulEquiv.refl Gal(Ω/K)).quotientCongr _ _ (by
      rw [fixingSubgroup_maximalAbelianExtension]
      exact Subgroup.map_id _)).trans
    (quotientFixingSubgroupEquiv K Ω (maximalAbelianExtension K Ω))

end Normal
end TauCeti
end
end
