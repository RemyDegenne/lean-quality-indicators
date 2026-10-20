namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat

set_option autoImplicit false

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace W2C2

theorem appLE_congr_hom {X' Y' : Scheme.{0}} {f g : X' ⟶ Y'} (h : f = g) (U : Y'.Opens) (V : X'.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

end W2C2
end P2MW.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat
