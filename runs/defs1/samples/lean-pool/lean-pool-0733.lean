@[expose] public section

open scoped MeasureTheory

variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]

namespace QuasiBorelSpace

@[inherit_doc IsHom]
scoped notation "IsHom[" inst₁ ", " inst₂ "]" => @IsHom _ _ inst₁ inst₂

/-- We can lift a `QuasiBorelSpace` from one type to another. -/
@[reducible] def lift (f : B → A) : QuasiBorelSpace B where
  IsVar φ := IsVar fun x ↦ f (φ x)
  isVar_const x := isVar_const (f x)
  isVar_comp := isVar_comp
  isVar_cases' := isVar_cases'

end QuasiBorelSpace
end
