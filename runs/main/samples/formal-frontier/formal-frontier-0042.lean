@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

section PowerKernel

@[simp]
lemma rootsOfUnityGroupSchemeInclusion_left (n : ℕ) :
    (rootsOfUnityGroupSchemeInclusion K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom K
          (Int.castAddHom (ZMod n))).toAlgHom.toRingHom) :=
  rfl

end PowerKernel
end AlgebraicGeometry
end
end
