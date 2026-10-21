namespace OAI

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree

namespace Projection

attribute [local instance] Classical.propDecidable

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β]

omit [Fintype β] in
theorem cellMass_pos (F : α → β) (x : α) : 0 < cellMass F (F x) := by
  unfold cellMass average
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  apply Finset.sum_pos'
  · intro y _
    unfold cell
    split_ifs <;> positivity
  · exact ⟨x,Finset.mem_univ x,by simp [cell]⟩

end Projection
end SquareRootDegree
end
end OAI
