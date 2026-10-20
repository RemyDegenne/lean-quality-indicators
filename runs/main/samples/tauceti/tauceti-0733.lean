public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

section Retraction

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q]

variable [Finite Q]

theorem ginzburgMap_injective : Function.Injective (ginzburgMap (Q := Q) k) :=
  Function.LeftInverse.injective (ginzburgRetraction_ginzburgMap k)

end Retraction
end TauCeti
end
