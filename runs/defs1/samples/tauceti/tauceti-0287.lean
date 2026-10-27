public section

open WithConv

namespace TauCeti.Cocharacter

universe u v w

noncomputable section

variable {R : Type u} {H : Type v} (A : Type w)

variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

variable [CommSemiring A] [Algebra R A]

variable (l : H →ₐc[R] LaurentPolynomial R)

/-- Inclusion of the dynamic unipotent subgroup into the dynamic parabolic. -/
noncomputable def unipotentToParabolic : unipotent A l →* parabolic A l :=
  Subgroup.inclusion (unipotent_le_parabolic (A := A) (l := l))

end
end TauCeti.Cocharacter
end
