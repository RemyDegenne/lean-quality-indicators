public section

open Set Function Filter Topology Bundle

open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
theorem normalSubspace_eq_of_mem_source [IsManifold I 1 M] {f : M → V} {x y : M}
    (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    normalSubspace I f y = (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)).rangeᗮ := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [normalSubspace, mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hg, ← hL]
  congr 1
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr L.surjective)

end Manifold
end TauCeti
end
