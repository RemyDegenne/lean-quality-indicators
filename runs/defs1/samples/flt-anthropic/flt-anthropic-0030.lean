namespace P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing

set_option autoImplicit false

set_option linter.unusedSectionVars false

universe u

namespace AdicCompletionNoetherian

open MvPolynomial MvPowerSeries

variable {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (f : Fin n → R)

noncomputable abbrev XI : Ideal (MvPolynomial (Fin n) R) := MvPolynomial.idealOfVars (Fin n) R

end AdicCompletionNoetherian
end P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing
