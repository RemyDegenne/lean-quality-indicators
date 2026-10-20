public section

open scoped unitInterval Topology Topology.Homotopy

open Topology.Homotopy

namespace HomotopyGroup

variable {M N X : Type*} [TopologicalSpace X] {x : X}

/-- **The homotopy groups of the loop space are the higher homotopy groups of the space**:
`π_(m + 1)(Ω X, refl x) ≃* π_(m + 2)(X, x)`. -/
noncomputable def pathLoopSpaceMulEquiv (m : ℕ) :
    π_ (m + 1) (Ω X x) (Path.refl x) ≃* π_ (m + 2) X x :=
  (homeomorphMulEquivOfEq (N := Fin (m + 1)) (GenLoop.homeomorphOfUnique (Fin 1))
    (GenLoop.homeomorphOfUnique_const (Fin 1))).symm.trans (piLoopSpaceMulEquiv m 1)

end HomotopyGroup
end
