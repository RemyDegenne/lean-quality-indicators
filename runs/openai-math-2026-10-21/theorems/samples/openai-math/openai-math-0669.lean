namespace OAI

noncomputable section

open scoped BigOperators Topology

open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_some (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (v : {v // v ∈ S}) :
    (G.onSide S).degree (fun e => x e.val) (some v) = G.degree x v.val := by
  simp only [degree]
  simp_rw [G.onSide_incident_some S v]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Incident v.val e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl (h.symm ▸ v.property))
  · exact he (Or.inr (h.symm ▸ v.property))

end LooplessGraph
end MatchingEntropy
end
end OAI
