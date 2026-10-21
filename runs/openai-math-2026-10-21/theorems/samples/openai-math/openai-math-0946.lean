namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Hastad

open BinPackingGames.Reduction.CloneGap

open scoped BigOperators

namespace EmptyContext

variable {I : Type}

theorem pairedEquations_acceptedCount (i₀ : I) (assignment : Address i₀ → Bool)
    (f : Cube I) :
    (pairedEquations i₀ f).countP (fun e => satisfied e assignment) = 1 := by
  simp only [pairedEquations, List.countP_cons, List.countP_nil, equation_satisfied_flip]
  cases satisfied (equation i₀ f) assignment <;> rfl

end EmptyContext
end BinPackingGames.Foundations.Hastad
end
end OAI
