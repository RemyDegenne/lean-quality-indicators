namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

open scoped TensorProduct

universe u

noncomputable section

namespace X1aRed

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

noncomputable def bc (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) {r : ℕ}
    (f : (Fin r → RW W) →ₗ[RW W] F.obj W.1) : (Fin r → RW W') →ₗ[RW W'] F.obj W'.1 :=
  ∑ i : Fin r, (LinearMap.proj i).smulRight (F.res h (f (ee (RW W) i)))

end X1aRed
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
