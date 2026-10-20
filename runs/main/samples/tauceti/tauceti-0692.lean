public section

namespace TauCeti

universe u

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K]

theorem inflH2AbsoluteGaloisProP_injective :
    Function.Injective (cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 2) :=
  inflH2MaximalProP_injective p (Field.absoluteGaloisGroup K)

end TauCeti
end
