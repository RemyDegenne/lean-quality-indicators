@[expose] public section

noncomputable section

open CategoryTheory Algebra.TensorProduct

open scoped CategoryTheory MonObj TensorProduct MonoidalCategory

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

namespace UnitriangularStageNormality

/-- The relative product of the two affine schemes is represented by their
tensor-product coordinate ring. -/
def stageProductIso :
    (unitriangularGroupScheme K (Fin n)).X ⊗ (unitriangularStageScheme K n r).X ≅
      (Spec (.of (productRing K n r))).asOver (Spec (.of K)) := by
  refine Over.isoMk (pullbackSpecIso K (ambientRing K n) (stageRing K n r)) ?_
  rw [Over.tensorObj_hom]
  exact pullbackSpecIso_hom_base K (ambientRing K n) (stageRing K n r)

end UnitriangularStageNormality
end AlgebraicGeometry
end
end
