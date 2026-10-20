public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.TypeBSpinCarrier

universe v

noncomputable section

attribute [local instance high] Algebra.toModule

variable (n : ℕ) {B : Type v} [CommRing B]

-- Match before simplification changes the counit-indexed integer module structure.
@[simp↓]
theorem tangentMatrix_derivationComp_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1))
    (d : Derivation ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)
      (Bialgebra.CounitAlgebra ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) B)) :
    GeneralLinear.tangentMatrix (dimension n)
        (HopfIdeal.quotientLieHom (B := B) (definingIdeal n)
          (derivationComp (B := B) (rootSubgroupIntegralCoordinateMap n k).hom d)) =
      AdditiveGroup.gaTangentLinearEquiv d • (rootIntMatrix n k).map (Int.cast : ℤ → B) := by
  have hcomp : (rootSubgroupIntegralCoordinateMap n k).hom.comp
      (Bialgebra.Quotient.mkBialgHom (definingIdeal n).toIdeal) =
      (kostantRootSubgroupCoordinateMap
        (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
        (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) k (isNilpotent_rep_rootGenerator n k)
        (latticeBasis n)).hom := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      mkQuotient_comp_rootSubgroupIntegralCoordinateMap]
  rw [HopfIdeal.quotientLieHom_apply, ← LinearMap.comp_apply, ← derivationComp_comp, hcomp]
  simpa only [rootIntMatrix_eq_toMatrix, algebraMap_int_eq, Int.coe_castRingHom] using
    tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap
      (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n) k (isNilpotent_rep_rootGenerator n k)
      (latticeBasis n) d

end
end TauCeti.TypeBSpinCarrier
end
