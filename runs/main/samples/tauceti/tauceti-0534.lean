public section

open Function Set Filter Topology

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {s : Set M} {x : M}

section Boundaryless

variable [I.Boundaryless]

theorem IsManifoldNondegenerateCriticalPoint.mem_criticalPoints
    (h : IsManifoldNondegenerateCriticalPoint I f x) : x ∈ criticalPoints I f :=
  mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.2
    ((isManifoldNondegenerateCriticalPoint_iff I).1 h).fderiv_eq_zero

end Boundaryless
end TauCeti
end
