namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {E : Type*} [DecidableEq E]

theorem chunkRank_lt_card (T : Finset E) (e : E) (he : e ∈ T) :
    chunkRank T e < T.card := by
  rw [chunkRank_of_mem T e he]
  exact (T.equivFin ⟨e, he⟩).isLt

end RyserCoveringCounterexample.Selection
end OAI
