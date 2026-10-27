public section

noncomputable section

universe u v w

open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- **`K` is an embedded Lie subgroup**: it carries `TauCeti.Lie.EmbeddedLieSubgroupData` for some
model vector space.

The model space is quantified over the universe of `G`, which is where the Lie algebra of `G`
lives, exactly as Mathlib's `Manifold.IsImmersionAt` pins the universe of its complement. -/
def IsEmbeddedLieSubgroup (K : Subgroup G) : Prop :=
  ∃ (E' : Type w) (_ : NormedAddCommGroup E') (_ : NormedSpace ℝ E'),
    Nonempty (EmbeddedLieSubgroupData I K E')

end TauCeti.Lie
end
end
