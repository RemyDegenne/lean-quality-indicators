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

open Filter ContinuousLinearMap

open ContinuousLinearMap

open scoped InnerProductSpace BigOperators Topology

open ContinuousLinearMap InnerProductSpace

open ContinuousLinearMap Filter

open scoped InnerProductSpace Topology BigOperators

open ContinuousLinearMap Filter

open scoped InnerProductSpace BigOperators

open scoped InnerProductSpace

open scoped InnerProductSpace BigOperators Topology

open Filter

open scoped InnerProductSpace

open scoped InnerProductSpace BigOperators

open scoped InnerProductSpace Topology BigOperators

open Filter

open scoped BigOperators Topology

open Filter

namespace SKQAOA

namespace Locality

theorem relevantEdges_qaoa_angles {n : ℕ} (E : Finset (Edge n)) (p : ℕ)
    (γ β γ' β' : Fin p → ℝ) (S : Finset (Fin n)) :
    relevantEdges E (qaoaWord p γ β) S=relevantEdges E (qaoaWord p γ' β') S := by
  induction p generalizing S with
  | zero => rfl
  | succ p ih =>
    simp only [qaoaWord,relevantEdges]
    rw [ih (fun i => γ i.castSucc) (fun i => β i.castSucc)
      (fun i => γ' i.castSucc) (fun i => β' i.castSucc)]

end Locality
end SKQAOA
end
end OAI
