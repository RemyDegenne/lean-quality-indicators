@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Proj.Veronese

open CategoryTheory GradedRing.Veronese HomogeneousLocalization

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The nilpotent-safe canonical equivalence between the corresponding affine charts. -/
def chartEquiv (n : ℕ) (hn : 0 < n) (j : ℕ) (f : VeroneseRing 𝒮 n)
    (hf : f ∈ component 𝒮 n j) :
    Away (component 𝒮 n) f ≃+* Away 𝒮 (inclusion 𝒮 n f) :=
  RingEquiv.ofBijective (chartHom 𝒮 n f)
    ⟨chartHom_injective 𝒮 n hn f, chartHom_surjective 𝒮 n j f hf⟩

end AlgebraicGeometry.Proj.Veronese
end
end
