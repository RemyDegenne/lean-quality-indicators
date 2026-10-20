@[expose] public section

universe u v w w₁ uF

open scoped TensorProduct

namespace CoalgHom

section Range

variable {K : Type u} {A : Type v} {B : Type w}

variable [Field K]

variable [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]

variable [AddCommGroup B] [Module K B] [Coalgebra K B]

@[simp]
theorem mem_range {f : A →ₗc[K] B} {y : B} : y ∈ f.range ↔ ∃ x, f x = y := by
  exact LinearMap.mem_range (f := f.toLinearMap)

end Range
end CoalgHom
end
