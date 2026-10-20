public section

open CategoryTheory

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.TypeDSpinCarrier

universe v w

noncomputable section

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

variable (n : ℕ) (hn : 4 ≤ n)

variable (A : Type v) [CommRing A]

-- Not a `simp` lemma: `simp` rewrites `hopfSpec` to `algSpec.mapGrp` composed with the
-- Hopf-algebra/cogroup equivalence, so no equation whose sides mention `hopfSpec.map` has a
-- left-hand side in `simp` normal form.
theorem hopfSpec_map_rootSubgroupIntegralCoordinateMap_op (k : Fin n ⊕ Fin n) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (rootSubgroupIntegralCoordinateMap n hn k).op =
      eqToHom (AdditiveGroup.groupScheme_def ℤ).symm ≫
        rootSubgroup n hn k ≫ eqToHom (groupScheme_def n hn) := by
  simpa only [rootSubgroupIntegralCoordinateMap, rootSubgroup_def, Category.assoc,
    eqToHom_trans] using
    hopfSpec_map_kostantRootSubgroupToralCoordinateMapOfEq_op
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
      (latticeBasis n) (basisWeight n) (definingIdeal_def n hn) k

end
end TauCeti.TypeDSpinCarrier
end
