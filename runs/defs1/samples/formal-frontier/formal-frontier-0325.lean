@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UpperTriangularCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Multiplicative natural isomorphism on all `K`-algebras and their maps,
extending the field-base functor in Milne, *Algebraic Groups* (2017),
§§2.8–2.9. -/
def upperTriangularGroupPointsIso :
    upperTriangularGroupFunctor K n ≅ upperTriangularGroupPointsFunctor K n :=
  NatIso.ofComponents
    (fun R => (upperTriangularGroupMulEquivPoints K n R).toGrpIso)
    (fun {R S} f => by
      ext s
      apply Over.OverMorphism.ext
      change (upperTriangularGroupMulEquivPoints K n S
        (Matrix.UpperTriangularGroup.map f.hom.toRingHom s)).left =
          ((algSpec (.of K)).map f.op).left ≫
            (upperTriangularGroupMulEquivPoints K n R s).left
      rw [upperTriangularGroupMulEquivPoints_apply_left]
      change Spec.map (CommRingCat.ofHom
        (upperTriangularFromGL K n S
          (Matrix.UpperTriangularGroup.map f.hom.toRingHom s)).toRingHom) =
            Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R s).toRingHom)
      rw [← Spec.map_comp]
      exact congrArg
        (fun h : UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] S =>
          Spec.map (CommRingCat.ofHom h.toRingHom))
          (upperTriangularFromGL_natural K n R f.hom s))

end AlgebraicGeometry
end
end
