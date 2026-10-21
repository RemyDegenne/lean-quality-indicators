namespace OAI

section

section

noncomputable section

open Set Function MeasureTheory ProbabilityTheory

open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct

variable {E I : Type*}

lemma selectedEvent_eq_iUnion (d : Set E → I) (A : I → Set (Set E)) :
    selectedEvent d A=⋃ i, ({ω | d ω=i}∩A i) := by
  ext ω
  simp only [selectedEvent,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  exact ⟨fun h => ⟨d ω,rfl,h⟩,fun ⟨i,hi,h⟩ => hi.symm ▸ h⟩

end CriticalPercolation.BernoulliProduct
end
end
end
end OAI
