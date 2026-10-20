@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Proj.Veronese

open CategoryTheory GradedRing.Veronese HomogeneousLocalization

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The canonical whole-space morphism has the published degree-scaled map as its
forward arrow, rather than a reconstructed point map. -/
def forward (n : ℕ) (hn : 0 < n) : Proj 𝒮 ⟶ Proj (component 𝒮 n) :=
  (domainIso 𝒮 n hn).inv ≫
    degreeScaledMap (component 𝒮 n) 𝒮 (inclusion 𝒮 n) n hn (inclusion_degree 𝒮 n)

end AlgebraicGeometry.Proj.Veronese
end
end
