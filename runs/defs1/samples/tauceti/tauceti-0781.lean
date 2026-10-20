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

/-- The quotient map by a subcomodule as a comodule morphism. -/
@[expose] def mkQ : Comodule.Hom R C M (M ⧸ N.toSubmodule) where
  toLinearMap := N.toSubmodule.mkQ
  map_coact := by
    ext m
    simp

end Subcomodule
end TauCeti
end
