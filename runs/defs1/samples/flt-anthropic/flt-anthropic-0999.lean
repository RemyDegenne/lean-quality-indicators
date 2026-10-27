namespace P2MW.S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

universe u v

open MvPowerSeries MvFormalGroup MvFormalGroup.WittLaw

namespace CurveInjSol

variable {p : ℕ} [hp : Fact p.Prime]

section Expansion

variable {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

def shiftPolyZ : ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | m + 1 => MvPolynomial.X (m + 1)

end Expansion
end CurveInjSol
end
end P2MW.S_MvFormalGroup_CartierModule_curve_injective_of_algebra_padicInt
