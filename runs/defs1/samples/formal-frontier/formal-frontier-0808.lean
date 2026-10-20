@[expose] public section

noncomputable section

open CategoryTheory Algebra.TensorProduct

open scoped CategoryTheory MonObj TensorProduct MonoidalCategory

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageNormality

/-- Conjugation by the ambient group, factored through the closed stage in
`Over (Spec K)`. The factor is not asserted to preserve the product group law.
Milne, *Algebraic Groups* (2017), §6.49(a) proves normality for the finer
field-case filtration, including these superdiagonal block endpoints. -/
def unitriangularStageConjugation :
    (unitriangularGroupScheme K (Fin n)).X ⊗
      (unitriangularStageScheme K n r).X ⟶ (unitriangularStageScheme K n r).X :=
  let e := stageProductIso K n r
  e.hom ≫ unitriangularStagePointMulEquiv K n r (productRing K n r)
    (affineConjugate K n r (productRing K n r)
      (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.fst _ _)
      (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.snd _ _))

end AlgebraicGeometry
end
end
