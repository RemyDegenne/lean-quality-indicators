namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder

open Filter

open scoped BigOperators

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

open scoped InnerProductSpace ComplexConjugate

open Filter Topology

open Filter Set Topology

open scoped InnerProductSpace ComplexConjugate Topology

open scoped InnerProductSpace

open scoped BigOperators Topology InnerProductSpace

open scoped BigOperators InnerProductSpace

open scoped BigOperators Matrix Topology ComplexConjugate

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open scoped BigOperators Matrix Topology

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

open scoped Topology

open Filter Asymptotics

open scoped InnerProductSpace Topology

open scoped InnerProductSpace Topology

open Filter

open scoped InnerProductSpace Topology

open Filter

open scoped InnerProductSpace BigOperators

open scoped InnerProductSpace Topology

open Filter

namespace RootSpin

open CoherentFock

theorem rotatedZ_unitary (β : ℝ) : rotatedZ β∈unitary _ :=
  mul_mem (mul_mem (root_adjoint_unitary _ (R_unitary _)) Z_unitary) (R_unitary _)

end RootSpin
end
end OAI
