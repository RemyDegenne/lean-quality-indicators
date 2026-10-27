public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

/-- The **cohomological degree** of an arrow of the Ginzburg quiver: the doubled arrows sit in
degree `0` and the adjoined loops in degree `-1`. -/
def ginzburgTwoDegree : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℤ
  | _, _, .double _ => 0
  | _, _, .loop _ => -1

end TauCeti
end
