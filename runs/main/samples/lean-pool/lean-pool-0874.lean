@[expose] public section

noncomputable section PortComputability

open Filter Topology

open NormedSpace

section

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem yosidaOperator_commute (R : ContractiveResolvent E)
    (α β : PositiveShift) (s t : NNReal) :
    Commute (R.yosidaOperator α s) (R.yosidaOperator β t) := by
  exact (commute_smul_smul_of_comp_eq _ _ (R.yosidaGenerator_commute α β).eq
    (s : ℝ) (t : ℝ)).exp

end ContractiveResolvent
end MarkovProcess.Semigroup
end
end PortComputability
end
