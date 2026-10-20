@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

namespace VertexDiskControl

/-- All intrinsic vertex and nonincident-edge separation properties survive shrinking the
common target radius. -/
def shrink {h : K.realization → Plane} (D : K.VertexDiskControl h) (r : ℝ)
    (hr : 0 < r) (hrD : r ≤ D.radius) : K.VertexDiskControl h where
  radius := r
  radius_pos := hr
  vertices_disjoint v w hvw :=
    (D.vertices_disjoint v w hvw).mono
      (Metric.closedBall_subset_closedBall hrD)
      (Metric.closedBall_subset_closedBall hrD)
  avoids_nonincident_edge v e hve :=
    (D.avoids_nonincident_edge v e hve).mono
      (Metric.closedBall_subset_closedBall hrD)
      (Metric.cthickening_mono hrD _)

end VertexDiskControl
end IntrinsicTwoComplex
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
