@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GradedRing.Veronese.CoherentTail

open CategoryTheory AlgebraicGeometry GradedRing.Veronese HomogeneousIdeal

universe u v w

variable {R S : Type u} [CommRing R] [CommRing S]
  {σ : Type v} {τ : Type w} [SetLike σ R] [AddSubgroupClass σ R]
  [SetLike τ S] [AddSubgroupClass τ S]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

namespace TailEquiv

variable {N : ℕ} (E : TailEquiv 𝒜 ℬ N) (n : ℕ) (hNn : N ≤ n) (hn : 0 < n)

/-- Isomorphism of the selected Proj schemes, including their structure sheaves. -/
def selectedProjIso : AlgebraicGeometry.Proj (component 𝒜 n) ≅
    AlgebraicGeometry.Proj (component ℬ n) :=
  ProjectiveSpace.projIsoOfInverseGradedRingHom
    (E.selectedGradedHomSymm n hNn) (E.selectedGradedHom n hNn)
    (E.selectedGradedHomSymm_comp n hNn) (E.selectedGradedHom_comp_symm n hNn)

end TailEquiv
end GradedRing.Veronese.CoherentTail
end
end
