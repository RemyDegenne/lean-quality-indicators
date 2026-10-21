namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

section

section

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

namespace WeightedTorusJets.Geometry

theorem add_jet_indices_le_next_stage {σ : Type*} (a α t : σ → ℕ) (b : ℕ)
    (ha : ∀ j, a j ≤ b * t j) (hα : ∀ j, α j ≤ t j) :
    ∀ j, (a + α) j ≤ (b + 1) * t j := by
  intro j
  simpa [Pi.add_apply, Nat.add_mul] using Nat.add_le_add (ha j) (hα j)

end WeightedTorusJets.Geometry
end
end
end Erdos970
end OAI
