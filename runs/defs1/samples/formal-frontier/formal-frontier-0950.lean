public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

variable (R : Type u) [CommRing R] [Algebra K R]

include K

/-- The group-valued functor of nilpotent elements in Milne's *Algebraic Groups*,
item 2.5, is represented by the quotient Hopf algebra's affine group scheme;
here the base may be any commutative ring of prime characteristic. -/
@[expose] def infinitesimalAdditivePointsIso :
    infinitesimalAdditiveFunctor K p m ≅ infinitesimalAdditivePointsFunctor K p m :=
  NatIso.ofComponents
    (fun R ↦ (infinitesimalAdditiveMulEquivPoints K p m R).toGrpIso)
    (fun {R S} f ↦ by
      ext r
      apply Over.OverMorphism.ext
      change
        (infinitesimalAdditiveMulEquivPoints K p m S
          (.ofAdd (infinitesimalAdditiveMap K p m R f.hom r.toAdd))).left =
          ((algSpec (.of K)).map f.op).left ≫
            (infinitesimalAdditiveMulEquivPoints K p m R r).left
      rw [infinitesimalAdditiveMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (infinitesimalAdditiveMulEquivAlgHom K p m S
            (.ofAdd (infinitesimalAdditiveMap K p m R f.hom r.toAdd))).ofConv.toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (infinitesimalAdditiveMulEquivAlgHom K p m R r).ofConv.toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : infinitesimalAdditiveCoordinateRing K p m →ₐ[K] S ↦
          CommRingCat.ofHom h.toRingHom)
        (infinitesimalAdditiveMulEquivAlgHom_naturality K p m R f.hom r.toAdd))

end AlgebraicGeometry
end
end
