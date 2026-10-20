@[expose] public section

universe u v w w₁ uF

open scoped TensorProduct

namespace CoalgHom

variable {K : Type u} {C : Type v} {A : Type w}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]

@[simp]
theorem codRestrict_inj (D : Subcoalgebra K C) {f g : A →ₗc[K] C}
    (hf : ∀ x, f x ∈ D) (hg : ∀ x, g x ∈ D) :
    f.codRestrict D hf = g.codRestrict D hg ↔ f = g := by
  constructor
  · intro h
    have h' := congrArg (fun k : A →ₗc[K] D => D.subtype.comp k) h
    simpa only [subtype_comp_codRestrict] using h'
  · intro h
    subst g
    exact CoalgHom.ext fun _ => Subtype.ext rfl

end CoalgHom
end
