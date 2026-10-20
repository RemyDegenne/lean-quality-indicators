@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

section AffinePoints

variable (R : Type u) [CommRing R] [Algebra K R]

lemma rootsOfUnityMulEquivPoints_naturality
    {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (n : ℕ) (ζ : rootsOfUnity n R) :
    rootsOfUnityMulEquivPoints K S n (restrictRootsOfUnity f n ζ) =
      (algSpec (.of K)).map (CommAlgCat.ofHom f).op ≫
        rootsOfUnityMulEquivPoints K R n ζ := by
  apply Over.OverMorphism.ext
  simp only [rootsOfUnityMulEquivPoints_apply_left,
    rootsOfUnityMulEquivAlgHom_naturality]
  exact Spec.map_comp
    (CommRingCat.ofHom (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv.toRingHom)
    (CommRingCat.ofHom f.toRingHom)

end AffinePoints
end AlgebraicGeometry
end
end
