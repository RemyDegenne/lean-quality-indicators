public section

open CategoryTheory

namespace TauCeti

universe u v w

variable (R : Type u) [CommSemiring R]

variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

attribute [instance] ComoduleCat.instComodule

namespace ComoduleCat

@[simp]
theorem isoToLinearEquiv_refl (M : ComoduleCat.{u, v, w} R C) :
    isoToLinearEquiv (R := R) (C := C) (Iso.refl M) = LinearEquiv.refl R M := by
  ext m
  rfl

end ComoduleCat
end TauCeti
end
