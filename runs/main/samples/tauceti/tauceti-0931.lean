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

@[reassoc (attr := simp)]
theorem coordinateMap_comp_rootSubgroupToBaseChangeCoordinateMap
    (k : Fin n ⊕ Fin n) :
    coordinateMap n hn A ≫ rootSubgroupToBaseChangeCoordinateMap n hn A k =
      kostantRootSubgroupBaseChangePresentationCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) A k := by
  unfold coordinateMap baseChangeDefiningIdeal rootSubgroupToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A k

end
end TauCeti.TypeDSpinCarrier
end
