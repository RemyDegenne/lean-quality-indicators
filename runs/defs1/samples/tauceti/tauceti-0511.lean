public section

open _root_.AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

section RationalFunctions

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X]

/-- Global rational functions are the function field, also as modules over the base ring. -/
def _root_.AlgebraicGeometry.Scheme.globalRationalFunctionsEquivFunctionField :
    Γ(Scheme.rationalFunctions X, ⊤) ≃ₗ[k] X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  exact {
    toFun := Scheme.rationalFunctionsEquiv ⊤
    invFun := (Scheme.rationalFunctionsEquiv ⊤).symm
    left_inv := (Scheme.rationalFunctionsEquiv ⊤).left_inv
    right_inv := (Scheme.rationalFunctionsEquiv ⊤).right_inv
    map_add' := (Scheme.rationalFunctionsEquiv ⊤).map_add
    map_smul' c f := by
      rw [Scheme.Modules.base_smul_globalSections,
        (Scheme.rationalFunctionsEquiv ⊤).map_smul]
      -- The scalar action through global functions is the germ in the function field.
      change X.germToFunctionField ⊤ (Scheme.Modules.baseRingToGlobalSections k X c) *
          Scheme.rationalFunctionsEquiv ⊤ f =
        algebraMap k X.functionField c * Scheme.rationalFunctionsEquiv ⊤ f
      rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField]
      rw [Scheme.baseRingToFunctionField_apply]
  }

end RationalFunctions
end
end AlgebraicGeometry
end TauCeti
end
