namespace P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Polynomial

universe u v w w'

noncomputable section

namespace LocCobSol

section TableAlgebra

variable {R : Type*} [CommRing R] {N : ℕ}

namespace TAlg

variable (T : Table R N)

scoped instance : AddCommGroup (TAlg T) := (equiv T).addCommGroup

scoped instance instModule : Module R (TAlg T) := (equiv T).module R

@[scoped simp] theorem linearEquiv_symm_apply (v : Fin (N + 1) → R) : (linearEquiv T).symm v = TAlg.mk v :=
  rfl

end TAlg
end TableAlgebra
end LocCobSol
end
end P2MW.S_AlgebraicCurve_exists_local_coboundary_of_smallExtension_of_monogenic_fibre
