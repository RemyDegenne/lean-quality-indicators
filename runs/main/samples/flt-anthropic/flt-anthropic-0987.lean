namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace S1Sketch

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

theorem coef_mul_smul {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (a : Γ(X, W)) (x : Γ(M, W)) : coef hs hWU hWV (a • x) = a * coef hs hWU hWV x := by
  rw [coef_eq_iff, mul_smul, coef_smul]

end S1Sketch
end P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_linearMap_sections_tensorPow_twistObj_monoidalV2
