namespace OAI

section

section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

section UpperProof

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal RealInnerProductSpace Topology

open Function MeasureTheory Set Filter

open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval

open GraphSchedule

open scoped Classical

variable {n : ℕ} {S : State (Fin (n+1))}

lemma primarySlotEquiv_source
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    (primarySlotEquiv hS β q i (Sum.inr (Sum.inl ()))).val=Sum.inl (Sum.inr i) := rfl

end LogConcaveSampling.AdjointRemoval
end UpperProof
end
end
end
end OAI
