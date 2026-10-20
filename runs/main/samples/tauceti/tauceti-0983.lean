public section

namespace TauCeti

open CategoryTheory

universe u

variable (G : Type u) [Monoid G]

attribute [local instance] TopRep.distribMulAction

theorem trivialF2TopPairing_bil_comm (x y : (trivialF2 G).V) :
    (trivialF2TopPairing G).bil x y = (trivialF2TopPairing G).bil y x := by
  simp only [trivialF2TopPairing_bil_apply, mul_comm]

end TauCeti
end
