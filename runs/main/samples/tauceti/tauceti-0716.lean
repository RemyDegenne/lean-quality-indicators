public section

universe v u

namespace TauCeti

open CategoryTheory Opposite

namespace MorphismIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
theorem op_rel_iff (I : MorphismIdeal C) {X Y : Cᵒᵖ} {f g : X ⟶ Y} :
    I.op.rel f g ↔ I.rel f.unop g.unop := by
  simp only [rel_iff, mem_op_hom, CategoryTheory.unop_sub]

end MorphismIdeal
end TauCeti
end
