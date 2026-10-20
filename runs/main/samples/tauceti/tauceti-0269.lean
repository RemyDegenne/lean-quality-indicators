public section

open scoped unitInterval Topology Topology.Homotopy

open Topology.Homotopy

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

@[simp]
theorem prodMulEquiv_apply [DecidableEq N] [Nonempty N] (x : X) (y : Y)
    (a : HomotopyGroup N (X × Y) (x, y)) :
    prodMulEquiv x y a = prodEquiv x y a :=
  (rfl)

end HomotopyGroup
end
