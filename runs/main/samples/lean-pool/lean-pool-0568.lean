@[expose] public section

open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

omit [Fintype α] in
lemma ofSub_union_card {W : Finset α} (T : Finset {x : α // x ∉ W}) :
    (ofSub W T ∪ W).card = T.card + W.card := by
  have hdis : Disjoint (ofSub W T) W := by
    refine disjoint_left.mpr ?_
    intro x hxT hxW
    rcases mem_map.mp hxT with ⟨⟨_, hx⟩, _, rfl⟩
    exact hx hxW
  rw [card_union_of_disjoint hdis, ofSub_card, Nat.add_comm]

end
end KahnKalai
end
