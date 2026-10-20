namespace P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped Pointwise

namespace CerednikDrinfeld

namespace BruhatTits

namespace FaithfulQ3

p2m_open

section Lattices

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

scoped instance free_of_isFullLattice' {L : Submodule R (Fin 2 → K)} [Submodule.IsLattice K L] : Module.Free R ↥L :=
  inferInstance

omit [IsDiscreteValuationRing R] in
theorem homothetic_pointwise_smul {r : R} (hr : r ≠ 0) (L : Submodule R (Fin 2 → K)) :
    Homothetic L (r • L) :=
  ⟨unitOfNeZero (K := K) hr, (pointwise_smul_eq_latticeMap hr L).symm⟩

end Lattices
end FaithfulQ3
end BruhatTits
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex
