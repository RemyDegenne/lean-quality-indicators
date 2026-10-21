namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace RowKernel

open AssociativeElimination WordGrading WeightedDeletion RowTwo

open RowTwo.Letter RowTwo.Slot

theorem cut_four : cut (κ .four) eCount aCount=EmbeddedTerminal.κ enc .w := by
  funext k l a b
  revert k l a b
  decide

end RowKernel
end DeligneDrinfeld
end
end OAI
