@[expose] public section

universe u v

namespace HopfAlgebra

section IsCocomm

open WithConv

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A]

local notation "𝑺" => antipode R (A := A)

@[simp]
theorem antipode_antipode_of_isCocomm (a : A) : antipode R (antipode R a) = a :=
  antipode_involutive_of_isCocomm a

end IsCocomm
end HopfAlgebra
end
