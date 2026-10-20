public section

namespace TauCeti

open Filter Metric Set Topology

section TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {U : Set X} {K : Set Y}
  {f : X → Y} {v : Y} {w : X}

/-- The **cluster set** of `f` on `U` at `w`: the set of values approached by `f z` as `z` tends to
`w` from inside `U`. Equivalently, the set of cluster points of the filter `𝓝[U] w` pushed forward
by `f`.

The point `w` is not required to lie in `U`, and the interesting case is `w ∈ frontier U`, where
the cluster set records the boundary behaviour of `f`. If `w ∉ closure U` the filter `𝓝[U] w` is
trivial and the cluster set is empty. -/
def clusterSetOn (f : X → Y) (U : Set X) (w : X) : Set Y := {v | MapClusterPt v (𝓝[U] w) f}

end TopologicalSpace
end TauCeti
end
