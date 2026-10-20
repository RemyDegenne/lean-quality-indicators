public section

noncomputable section

open Function Set Topology WithLp

open scoped Manifold ContDiff

namespace TauCeti

namespace EuclideanHalfSpace

theorem isOpen_normalIio (ε : ℝ) : IsOpen (normalIio ε) := by
  have : Continuous fun t : EuclideanHalfSpace 1 ↦ t.1 0 := by fun_prop
  exact isOpen_Iio.preimage this

end EuclideanHalfSpace
end TauCeti
end
end
