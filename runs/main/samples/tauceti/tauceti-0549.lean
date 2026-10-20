public section

open scoped TensorProduct

namespace TauCeti

universe u v w x y

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}

variable [CommRing R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]

variable [AddCommMonoid M] [Module R M] [Comodule R C M]

variable [AddCommMonoid N] [Module R N] [Comodule R C N]

namespace Subcomodule

theorem comap_mono (f : Comodule.Hom R C M N) {B D : Subcomodule R C N} (hBD : B ≤ D) :
    B.comap f ≤ D.comap f := by
  intro m hm
  exact hBD hm

end Subcomodule
end TauCeti
end
