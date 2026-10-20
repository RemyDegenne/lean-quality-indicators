@[expose] public section

namespace HadwigerNelsonBounds

lemma partsGadgetNegationNeighbor7 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 7) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 7) := by
  change neighbor ∈ [2, 3, 6, 8, 12, 13, 44] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

end HadwigerNelsonBounds
end
