@[expose] public section

universe u v w w₁ uF

open scoped TensorProduct

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable {A : Type w} [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]

@[simp]
theorem subtype_comp_inj (D : Subcoalgebra K C) {f g : A →ₗc[K] D} :
    D.subtype.comp f = D.subtype.comp g ↔ f = g :=
  D.subtype_comp_injective.eq_iff

end Subcoalgebra
end
