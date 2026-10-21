namespace OAI

namespace PartitionPilot.Forcing

namespace SetFormula

open SetRealization

universe u

variable {P : Type u} [Preorder P] {s : Presentation P}

theorem decisionWitness_dense (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) : Dense (DecisionWitness D φ env) := by
  classical
  intro p
  by_cases possible : ∃ q, q ≤ p ∧ Forces D φ env q
  · obtain ⟨q, qp, hq⟩ := possible
    exact ⟨q, qp, Or.inl hq⟩
  · exact ⟨p, le_rfl, Or.inr (fun q qp hq => possible ⟨q, qp, hq⟩)⟩

end SetFormula
end PartitionPilot.Forcing
end OAI
