public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]

/-- The affine additive group scheme represents the additive-group functor.
This extends the field-base additive group of Milne, *Algebraic Groups*
(2017), item 2.1, to an arbitrary commutative base ring. -/
@[expose] def additiveGroupPointsIso
    (K : Type u) [CommRing K] :
    additiveGroupFunctor K ≅ additiveGroupPointsFunctor K :=
  NatIso.ofComponents
    (fun R ↦ (additiveGroupMulEquivPoints K R).toGrpIso)
    (fun {R S} f ↦ by
      ext r
      apply Over.OverMorphism.ext
      change
        (additiveGroupMulEquivPoints K S (.ofAdd (f.hom r))).left =
          ((algSpec (.of K)).map f.op).left ≫
            (additiveGroupMulEquivPoints K R (.ofAdd r)).left
      rw [additiveGroupMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (additiveGroupMulEquivAlgHom K S
            (.ofAdd (f.hom r))).ofConv.toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv.toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : additiveGroupCoordinateRing K →ₐ[K] S ↦
          CommRingCat.ofHom h.toRingHom)
        (additiveGroupMulEquivAlgHom_naturality K R f.hom r))

end AlgebraicGeometry
end
end
