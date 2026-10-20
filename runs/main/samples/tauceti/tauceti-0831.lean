public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

@[simp]
theorem ginzburgTwoDegree_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgTwoDegree (GinzburgHom.double a) = 0 := by
  simp [ginzburgTwoDegree]

end TauCeti
end
