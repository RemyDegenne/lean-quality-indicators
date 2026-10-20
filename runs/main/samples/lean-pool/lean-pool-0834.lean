@[expose] public section

open CategoryTheory AlgebraicTopology

open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree

variable {R : Type} [CommRing R] {X : TopCat.{0}}

@[simp] theorem smallBoundary_hom_apply
    {𝒰 : OpenCoverData X} (n : ℕ) (c : smallChainSubmodule R X 𝒰 (n + 1)) :
    ((smallBoundary R X 𝒰 n).hom c : singularChainGroup R X n)
      = (singularBoundary R X n).hom (c : singularChainGroup R X (n + 1)) := by
  rfl

end SphereOddDegree
end
