namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

open Filter Topology

namespace FreeGroupFactorMain.WeightedFock

open FreeFock Amplification.Polar

variable {ι : Type u_2} [DecidableEq ι]

theorem edge_sum_mem_edge (u v : ℝ) (i : ι) :
    offDiagonal u v i+star (offDiagonal u v i)∈edgeAlgebra u v i :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end FreeGroupFactorMain.WeightedFock
end
end OAI
