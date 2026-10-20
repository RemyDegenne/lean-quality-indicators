namespace P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Polynomial

universe u v

noncomputable section

namespace WittLiftNF

section TableAlgebra

variable {R : Type*} [CommRing R] {N : ℕ}

namespace TAlg

variable (T : Table R N)

scoped instance : AddCommGroup (TAlg T) := (equiv T).addCommGroup

scoped instance instModule : Module R (TAlg T) := (equiv T).module R

theorem coord_sum {ι : Type*} (s : Finset ι) (f : ι → TAlg T) :
    (∑ i ∈ s, f i).coord = ∑ i ∈ s, (f i).coord := by
  change linearEquiv T (∑ i ∈ s, f i) = ∑ i ∈ s, linearEquiv T (f i)
  exact map_sum _ _ _

end TAlg
end TableAlgebra
end WittLiftNF
end
end P2MW.S_AlgebraicCurve_exists_wittVector_lift_of_normalFormOrder
