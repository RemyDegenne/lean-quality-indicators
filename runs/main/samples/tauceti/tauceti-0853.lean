public section

open MulOpposite

namespace TauCeti

universe u v w

namespace BimoduleDerivation

variable {k : Type u} {A : Type v} {M : Type w}
  [CommSemiring k] [Semiring A] [AddCommMonoid M] [Algebra k A]
  [Module k M] [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

@[simp]
theorem leibniz (D : BimoduleDerivation k A M) (a b : A) :
    D (a * b) = a • D b + op b • D a :=
  D.leibniz' a b

end BimoduleDerivation
end TauCeti
end
