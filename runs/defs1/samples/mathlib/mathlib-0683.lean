@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

namespace ShortComplex

variable {S₁ S₂ S₃ : ShortComplex C}

attribute [local simp] Hom.comm₁₂ Hom.comm₂₃

section Homotopy

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

variable (S₁ S₂)

namespace Homotopy

attribute [local simp] neg_comp

variable {S₁ S₂ φ₁ φ₂ φ₃ φ₄}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy between morphisms in `ShortComplex Cᵒᵖ` that is induced by a homotopy
between morphisms in `ShortComplex C`. -/
@[simps]
def op (h : Homotopy φ₁ φ₂) : Homotopy (opMap φ₁) (opMap φ₂) where
  h₀ := h.h₃.op
  h₁ := h.h₂.op
  h₂ := h.h₁.op
  h₃ := h.h₀.op
  h₀_f := Quiver.Hom.unop_inj h.g_h₃
  g_h₃ := Quiver.Hom.unop_inj h.h₀_f
  comm₁ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₁]; abel)

end Homotopy
end Homotopy
end ShortComplex
end CategoryTheory
end
