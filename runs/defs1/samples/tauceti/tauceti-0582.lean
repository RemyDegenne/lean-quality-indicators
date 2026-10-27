public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (D Y : C) [ExactPairing D Y]

variable [Closed Y]

/-- The internal hom out of `Y` is left tensoring by a left dual `D` of `Y`: both functors are
right adjoint to `Y ⊗ -`. -/
def ihomIsoTensorLeft : ihom Y ≅ tensorLeft D :=
  (ihom.adjunction Y).rightAdjointUniq (tensorLeftAdjunction D Y)

end TauCeti
end
