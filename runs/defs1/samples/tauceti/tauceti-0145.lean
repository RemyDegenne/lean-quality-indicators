public section

open scoped unitInterval Topology Topology.Homotopy

open Topology.Homotopy

namespace GenLoop

variable {M N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- The homotopy relative to the cube boundary underlying a path in the space of generalized
loops. The relative condition is automatic: every stage of the path is a generalized loop, so
it takes the value `x` at every point of the cube boundary. -/
def homotopyRelOfPath {p q : Ω^ N X x} (γ : Path p q) :
    (p : C(I^N, X)).HomotopyRel q (Cube.boundary N) where
  toFun := (ContinuousMap.uncurry
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(Ω^ N X x, C(I^N, X))).comp γ.toContinuousMap))
  map_zero_left z := congrArg (fun r : Ω^ N X x => r z) γ.source
  map_one_left z := congrArg (fun r : Ω^ N X x => r z) γ.target
  prop' t z hz := ((γ t).property z hz).trans (_root_.GenLoop.boundary p z hz).symm

end GenLoop
end
