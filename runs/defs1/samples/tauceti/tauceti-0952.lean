public section

namespace TauCeti.Isogeny

open AlgebraicGeometry

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)
  [Algebra W₂.FunctionField W₁.FunctionField]
  (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)

/-- **The pullback of a divisor along an isogeny**: the conorm of the finite extension of function
fields that the isogeny induces. -/
noncomputable def divisorPullback :
    Divisor F W₂.FunctionField →+ Divisor F W₁.FunctionField :=
  haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  haveI := φ.finiteDimensional_functionField h
  Divisor.conorm F W₁.FunctionField

end TauCeti.Isogeny
end
