namespace OAI

namespace KadisonKastler

open scoped BigOperators BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] [CStarAlgebra B]

omit [Group G] [DiscreteTopology G] in
@[simp]
theorem finiteGroupAverage_apply (f : G →ᵇ B) :
    finiteGroupAverage f = ((Fintype.card G : ℝ)⁻¹) • ∑ g : G, f g := by
  simp [finiteGroupAverage]

end
end KadisonKastler
end OAI
