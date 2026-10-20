@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

namespace TriWitnessAux

open TriangleInflation

variable {t : ℕ}

theorem pushforward_isLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {w : α → ℝ} (h : IsLaw w) (F : α → β) : IsLaw (pushforward w F) := by
  refine ⟨fun b => ?_, ?_⟩
  · exact Finset.sum_nonneg (fun a _ => by split; exacts [h.1 a, le_rfl])
  · have := sum_mul_pushforward w F (fun _ => (1 : ℝ))
    simpa [h.2] using this

end TriWitnessAux
end TriangleInflation.Graph
end
