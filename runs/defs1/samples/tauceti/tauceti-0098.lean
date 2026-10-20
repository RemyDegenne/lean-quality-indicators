public section

open CategoryTheory CategoryTheory.Limits

open TauCeti.SymmetricAlgebra

open scoped TensorProduct

namespace AlgebraicGeometry.Proj

universe u

variable (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Linear automorphisms with parameter coefficients give projective scheme automorphisms
of the fiber product. Multiplication is ordinary function composition. -/
noncomputable def symmetricAlgebraFamilyAut :
    ((S ⊗[R] M) ≃ₗ[S] (S ⊗[R] M)) →*
      Aut (pullback (toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :=
  (symmetricAlgebraBaseChangeIso R S M).conjAut.toMonoidHom.comp
    (symmetricAlgebraAut S)

end AlgebraicGeometry.Proj
end
