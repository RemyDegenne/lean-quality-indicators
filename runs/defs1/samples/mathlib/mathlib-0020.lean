@[expose] public section

open Finset Function

open Fintype (card)

namespace SimpleGraph

variable {V W X : Type*} {G G₁ G₂ G₃ : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

section LabelledCopyCount

variable [Fintype V] [Fintype W]

/-- `G.labelledCopyCount H` is the number of labelled copies of `H` in `G`, i.e. the number of graph
embeddings from `H` to `G`. See `SimpleGraph.copyCount` for the number of unlabelled copies. -/
noncomputable def labelledCopyCount (G : SimpleGraph V) (H : SimpleGraph W) : ℕ := by
  classical exact Fintype.card (Copy H G)

end LabelledCopyCount
end SimpleGraph
end
