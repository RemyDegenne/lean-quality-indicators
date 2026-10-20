@[expose] public section

universe u v w w₁ uF

open scoped TensorProduct

namespace CoalgHom

variable {K : Type u} {C : Type v} {A : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]

theorem codRestrict_unique (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) (g : A →ₗc[K] D) (hg : D.subtype.comp g = f) :
    g = f.codRestrict D h := by
  apply D.subtype_comp_injective
  exact hg.trans (subtype_comp_codRestrict f D h).symm

end CoalgHom
end
