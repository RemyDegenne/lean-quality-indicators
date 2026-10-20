public noncomputable section

open scoped NNReal unitInterval ContinuousMap

open Topology Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace MooreLoopSpace

/-- **The Moore loop space is homotopy equivalent to Mathlib's loop space** `Path x x` of loops
parametrized by the unit interval, by `toPath` and `Path.toMooreLoop`. -/
def homotopyEquivPath (x : X) : MooreLoopSpace X x ≃ₕ Path x x where
  toFun := ⟨toPath, continuous_toPath⟩
  invFun := ⟨Path.toMooreLoop, Path.continuous_toMooreLoop⟩
  left_inv := ⟨unitHomotopy⟩
  right_inv :=
    ⟨(ContinuousMap.Homotopy.refl _).cast rfl (ContinuousMap.ext Path.toPath_toMooreLoop)⟩

end MooreLoopSpace
end TauCeti
end
