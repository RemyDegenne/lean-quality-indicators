namespace P2MW.S_ModularCurve_genusFormula_isNat

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_reactivate

open Finset

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

namespace ModularCurve

p2m_open

open Finset

scoped instance (d : ℕ) : Decidable (squarefreeFin d) := Finset.decidableDforallFinset

def nuTwoFin (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun x => (x ^ 2 + 1) % N = 0).card

end ModularCurve
end P2MW.S_ModularCurve_genusFormula_isNat
