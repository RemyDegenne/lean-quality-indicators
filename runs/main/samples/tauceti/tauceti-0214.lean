public section

namespace TauCeti

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace PlumbingGraph

theorem latticeDifferential_mem_latticeChainMaslovGrading_piece (P : PlumbingGraph V)
    (k : P.characteristicVectors) {p : ℤ} {c : PlumbingChain V}
    (hc : c ∈ (P.latticeChainMaslovGrading k).piece p) :
    P.latticeDifferential k c ∈ (P.latticeChainMaslovGrading k).piece (p - 1) := by
  classical
  rw [mem_latticeChainMaslovGrading_piece_iff] at hc
  nth_rw 1 [← c.sum_single]
  rw [Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun C _ => ?_
  nth_rw 1 [← Polynomial.sum_monomial_eq (c C)]
  rw [Polynomial.sum, Finsupp.single_finsetSum, map_sum]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [← hc C j (Polynomial.mem_support_iff.mp hj)]
  exact P.latticeDifferential_single_monomial_mem_maslov_piece k C j _

end PlumbingGraph
end TauCeti
end
