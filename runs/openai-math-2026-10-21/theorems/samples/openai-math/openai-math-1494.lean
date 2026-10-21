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

lemma primarySlotEquiv_derivative
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) (k : Fin (S.derivatives i).length) :
    (primarySlotEquiv hS β q i (Sum.inr (Sum.inr k))).val=
      Sum.inl (Sum.inr ((S.derivatives i).get k)) := rfl

end LogConcaveSampling.AdjointRemoval
end UpperProof
end
end
end
end OAI
