open scoped Finset

@[expose] public section

open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {R 𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem WithSeminorms.withSeminorms_eq {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) : t = p.moduleFilterBasis.topology :=
  hp.1

end Topology
end
