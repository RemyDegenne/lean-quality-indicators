namespace P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle

set_option autoImplicit false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

section G1ScalarPart

namespace G1ScalarPart

variable {X Y : Scheme.{u}}

theorem smul_eq (P : X.Modules) (U : (Opens X)ᵒᵖ) (a : X.ringCatSheaf.obj.obj U) (x : P.val.obj U) :
    (show Γ(P, U.unop) from (a • x : P.val.obj U)) =
      (show Γ(X, U.unop) from a) • (show Γ(P, U.unop) from x) := rfl

end G1ScalarPart
end G1ScalarPart
end
end P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
