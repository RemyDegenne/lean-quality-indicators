namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335

namespace IndependentCoordinates

theorem average_grouped_prod {σ ι α : Type*}
    [Fintype σ] [Fintype ι] [Fintype α] [DecidableEq σ] [DecidableEq ι]
    (group : σ → ι) (f : ∀ i, ({s // group s = i} → α) → ℝ) :
    average (fun x : σ → α => ∏ i, f i (fun s => x s)) =
      ∏ i, average (f i) := by
  calc
    _ = average (fun x : ∀ i, ({s // group s = i} → α) => ∏ i, f i (x i)) :=
      average_equiv (fiberAssignmentEquiv group) _
    _ = _ := average_prod f

end IndependentCoordinates
end Problem335
end
end OAI
