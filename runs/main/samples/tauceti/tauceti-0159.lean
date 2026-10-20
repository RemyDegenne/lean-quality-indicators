public section

noncomputable section

open Topology

open scoped ContDiff Manifold

namespace ContinuousMonoidHom

attribute [local instance] LieGroup.minSmoothnessThree

attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  [LieGroup I ∞ G] [LieGroup I' ∞ G']

theorem lieMap_comp
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G'']
    [FiniteDimensional ℝ E''] [LieGroup I'' ∞ G'']
    (f : G →ₜ* G') (g : G' →ₜ* G'') :
    lieMap (I := I) (I' := I'') (g.comp f) =
      (lieMap (I := I') (I' := I'') g).comp (lieMap (I := I) (I' := I') f) := by
  have h : (g.comp f).toContMDiffMonoidMorphism I I'' =
      (g.toContMDiffMonoidMorphism I' I'').comp
        (f.toContMDiffMonoidMorphism I I') := by
    apply DFunLike.coe_injective
    rw [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContMDiffMonoidMorphism.coe_comp,
      ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContinuousMonoidHom.coe_comp]
  rw [lieMap, lieMap, lieMap, h, _root_.lieMap_comp]

end ContinuousMonoidHom
end
end
