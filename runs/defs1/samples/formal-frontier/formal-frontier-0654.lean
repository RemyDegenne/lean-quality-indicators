@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The north pole `(0, 0, 1)` bundled as a point of the metric unit two-sphere. -/
def sphere2NorthPoint : Metric.sphere (0 : E3) 1 := ⟨sphere2NorthVector, by
  rw [mem_sphere_zero_iff_norm]
  exact sphere2NorthVector_norm⟩

end SphereTopology
end
end
