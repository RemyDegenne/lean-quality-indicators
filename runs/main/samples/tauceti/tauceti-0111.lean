public noncomputable section

open scoped NNReal unitInterval ContinuousMap

open Topology Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace MooreLoopSpace

@[simp]
theorem _root_.Path.toMoorePath_toMooreLoop (p : Path x x) :
    p.toMooreLoop.toMoorePath = p.toMoorePath :=
  (rfl)

end MooreLoopSpace
end TauCeti
end
