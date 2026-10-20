set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

open Module

open scoped LinearAlgebra.Projectivization

section NeighbourFamily

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable [IsFractionRing R K]

theorem dvd_of_interLattice_eq {ϖ c d c' d' : R}
    (h : interLattice R K ϖ c d = interLattice R K ϖ c' d') :
    ϖ ∣ d' * c - c' * d := by
  have hmem := vecPair_mem_interLattice (R := R) (K := K) ϖ c d
  rw [h, vecPair_mem_interLattice_iff_dvd] at hmem
  exact hmem

end NeighbourFamily
end LT.LatticeTree
