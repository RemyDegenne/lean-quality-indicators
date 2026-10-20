public section

noncomputable section

open Filter Int Metric Set TopologicalSpace

open scoped Topology Uniformity Interval

universe u v w

variable {α : Type u}

namespace Int

open Metric

theorem tendsto_coe_cofinite : Tendsto ((↑) : ℤ → ℝ) cofinite (cocompact ℝ) := by
  apply (castAddHom ℝ).tendsto_coe_cofinite_of_isDiscrete cast_injective
  rw [range_castAddHom, SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

end Int
end
end
