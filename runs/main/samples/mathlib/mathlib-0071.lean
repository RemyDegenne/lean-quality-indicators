@[expose] public section

open Function

@[inherit_doc]
notation:25 P₁ " ≃ᴬ[" k:25 "] " P₂:0 => ContinuousAffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]
  [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄] [TopologicalSpace P₄]

namespace ContinuousAffineEquiv

section ReflSymmTrans

@[simp]
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

end ReflSymmTrans
end ContinuousAffineEquiv
end
