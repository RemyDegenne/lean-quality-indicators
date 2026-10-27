namespace P2MW.S_HeckeEis_exists_retraction_binaryFormEval

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

noncomputable section

namespace HeckeEis

p2m_open

open MvPolynomial ModularCurve

open scoped MatrixGroups

section Split

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

attribute [local instance] fintypeProjectiveLine

def retraction : (ProjectiveLine (ZMod p) → K) →ₗ[K] BinaryForm K (p - 1) :=
  lagrMap p K ∘ₗ proj0 p K

end Split
end HeckeEis
end
end P2MW.S_HeckeEis_exists_retraction_binaryFormEval
