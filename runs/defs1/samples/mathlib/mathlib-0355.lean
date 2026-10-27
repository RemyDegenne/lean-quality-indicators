@[expose] public section

open Function

open scoped Topology

notation "C(" X ", " Y ")" => ContinuousMap X Y

export ContinuousMapClass (map_continuous)

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- See note [custom simps projection]. -/
def Simps.apply (f : C(X, Y)) : X → Y := f

end ContinuousMap
end
