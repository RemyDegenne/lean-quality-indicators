public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

local instance : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstanceAs (Nonempty X)), by simp⟩⟩

@[simp]
lemma principalCartierDivisor_regularUnitToFunctionField
    (f : ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ) :
    principalCartierDivisor X
      (Units.map (X.germToFunctionField (⊤ : X.Opens)).hom f) = 0 :=
  rationalUnitClass_germToFunctionField_eq_zero X ⊤ f

end Scheme
end
end AlgebraicGeometry
end TauCeti
end
