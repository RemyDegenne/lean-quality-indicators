@[expose] public section

open Multiplicative WithZero

noncomputable section

namespace PrimeMultiplicity

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]

variable {p : R}

variable {S : Submonoid R} {B : Type*} [CommRing B] [Algebra R B]
  [IsLocalization S B]

@[simp]
theorem awayValuation_mk' (hp : Prime p) {B : Type*} [CommRing B]
    [Algebra R B] [IsLocalization.Away p B] (x : R)
    (y : Submonoid.powers p) :
    awayValuation (B := B) hp (IsLocalization.mk' B x y) =
      valuation hp x * (valuation hp y)⁻¹ := by
  exact localizationValuation_mk' hp (powers_le_nonZeroDivisors hp) x y

end PrimeMultiplicity
end
end
