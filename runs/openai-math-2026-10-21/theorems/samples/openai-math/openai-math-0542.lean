namespace OAI

noncomputable section

namespace DFVSGames.Foundations.PCP.AlphabetGraph

open DFVSGames.Foundations.Hastad

open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

omit [Nonempty A] in
@[simp] theorem card_event [Fintype E] :
    Fintype.card (Event E A) = Fintype.card E * Fintype.card (LocalEvent A) :=
  Fintype.card_prod _ _

end DFVSGames.Foundations.PCP.AlphabetGraph
end
end OAI
