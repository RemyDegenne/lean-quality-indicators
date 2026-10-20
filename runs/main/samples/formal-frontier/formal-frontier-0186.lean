public section

open Function Set

universe u v

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

@[simp]
theorem rankLocallyConstant_apply (p : PrimeSpectrum R) :
    rankLocallyConstant R M p = rankAtStalk (R := R) M p :=
  rfl

end Module
end
