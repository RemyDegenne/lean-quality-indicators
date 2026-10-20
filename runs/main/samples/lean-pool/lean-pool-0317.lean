@[expose] public section

namespace NRR

open scoped BigOperators

open SphereOddDegree

open SphereOddDegree.AffineBarycentricSubdivision

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismHorizontalEndpointIdentification

open AffinePositiveRayBoundary

open EquivariantPrismVertexParameters

open EquivariantPrismGenericityPolynomials

open EquivariantPrismGenericPerturbation

open EquivariantPrismGlobalCancellation

open EquivariantPrismNonhorizontalCancellation

open SubdivisionPrismCharts

open RefinedAffineMap

variable {p : Nat}

theorem affineCompMap_succ_last_vertex_pos
    (n N : Nat) (rho : Fin (N + 1) → Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    0 < affineCompMap n (N + 1) rho
      (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last n)) j := by
  rw [affineCompMap_succ]
  apply affineCompMap_pos_of_forall_pos n N (fun i => rho i.castSucc)
  intro i
  change 0 < affineSubdivMap n (rho (Fin.last N))
    (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last n)) i
  rw [affineSubdivMap_vertex, prefixBarycenter_apply]
  have hi : i ∈ prefixSet n (rho (Fin.last N)) (Fin.last n) := by
    rw [mem_prefixSet]
    exact Fin.le_last _
  rw [ite_eq_left hi]
  positivity

end EquivariantPrismHorizontalEndpointIdentification
end FoxNeuwirthOrderComplex
end NRR
end
