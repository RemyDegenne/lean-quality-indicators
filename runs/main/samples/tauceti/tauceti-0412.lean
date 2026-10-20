public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommRing R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommGroup M] [Module R M] [Comodule R C M]

namespace Subcomodule

variable (N : Subcomodule R C M)

@[simp]
theorem mkQ_apply (m : M) : N.mkQ m = Submodule.Quotient.mk m :=
  rfl

end Subcomodule
end TauCeti
end
