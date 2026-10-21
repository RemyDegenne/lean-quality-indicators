namespace OAI

namespace Ostmann.Preliminaries

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

theorem projectedMass_test (π : α → β) (μ : α → ℝ) (f : β → ℝ) :
    ∑ r, projectedMass π μ r * f r = ∑ a, μ a * f (π a) := by
  simp only [projectedMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

end Ostmann.Preliminaries
end OAI
