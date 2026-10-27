public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite WithConv

universe u

/-- The forward smooth-unipotent anti-equivalence, followed by the inclusions into finite-type
affine group schemes and affine group schemes, is Mathlib's `hopfSpec` after forgetting the
smooth-unipotent and finite-type proofs. This is the computation interface for the restricted
equivalence. -/
noncomputable def
    smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCat k).functor ⋙
          (smoothUnipotentAffineGroupSchemeProperty k).ι ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (SmoothUnipotentCommHopfAlgCat.{u, u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  Functor.isoWhiskerRight
      (smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCatFunctorCompιIso k)
      ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (SmoothUnipotentCommHopfAlgCat.{u, u} k)
        (FiniteTypeCommHopfAlgCat.{u, u} k)).op
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k)

end TauCeti
end
