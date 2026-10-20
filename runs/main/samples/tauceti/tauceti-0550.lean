public section

open scoped Matrix

universe v

namespace TauCeti.E6Minuscule

open TauCeti.E6

local notation "Λ" => TauCeti.coordinateLattice (Fin 27)

local notation "𝓑" => TauCeti.coordinateLatticeBasis (Fin 27)

open AlgebraicGeometry CategoryTheory

open TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

theorem rootSubgroup_def (k : Fin 6 ⊕ Fin 6) :
    rootSubgroup k =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
        (TauCeti.serreRootGenerator weightTable.cartanMatrix)
        (TauCeti.serreH ℚ weightTable.cartanMatrix) weightTable.rep (Λ).toAddSubgroup
        (fun _ hu _ hv ↦ weightTable.rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        weightTable.isNilpotent_rep_serreRootGenerator 𝓑 weightTable.weight k := by
  rw [rootSubgroup]

end TauCeti.E6Minuscule
end
