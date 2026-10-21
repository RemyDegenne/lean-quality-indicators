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

open scoped InnerProductSpace BigOperators

open scoped InnerProductSpace Topology BigOperators

open scoped Topology BigOperators

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators

open scoped InnerProductSpace Topology BigOperators

open Filter

open scoped InnerProductSpace Topology BigOperators

open Filter

open scoped InnerProductSpace Topology BigOperators

open Filter

open scoped InnerProductSpace BigOperators

open scoped InnerProductSpace BigOperators

namespace FiniteTree

open SpinOperators PointedTree

theorem root_unitary (D h : ℕ) {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ unitary _) :
    root D h A ∈ unitary _ :=
  by
    rw [Unitary.mem_iff] at hA ⊢
    constructor
    · rw [←root_star,←root_mul,hA.1,root_one]
    · rw [←root_star,←root_mul,hA.2,root_one]

end FiniteTree
end
end OAI
