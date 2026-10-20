public section

open Set Metric Topology

namespace TauCeti

variable (ι : Type*) [Fintype ι]

section VertexSwap

variable {ι}

/-- The affine involution exchanging the origin vertex with the `j`th coordinate vertex
of the coordinate simplex. It replaces coordinate `j` by the missing barycentric mass. -/
noncomputable def coordinateSimplexVertexSwap (j : ι) : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) := by
  classical
  exact ContinuousAffineMap.const ℝ (ι → ℝ) (Pi.single j (1 : ℝ) : ι → ℝ) +
    (ContinuousLinearMap.pi fun i => if i = j then
      -(∑ k, (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ))
      else ContinuousLinearMap.proj i).toContinuousAffineMap

end VertexSwap
end TauCeti
end
