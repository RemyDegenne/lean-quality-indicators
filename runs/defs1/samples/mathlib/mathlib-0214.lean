@[expose] public section

universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

namespace MorphismProperty

section

variable (C : Type u) [CategoryStruct.{v} C]

variable {C}

/-- The morphism property in `C` associated to a morphism property in `Cᵒᵖ` -/
@[simp]
def unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C := fun _ _ f => P f.op

end
end MorphismProperty
end CategoryTheory
end
end
