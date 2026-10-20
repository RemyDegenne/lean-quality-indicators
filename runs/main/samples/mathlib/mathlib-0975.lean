@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Opposite

variable {C : Type u}

section

variable [Category.{v} C]

@[simp]
lemma unop_inf (P Q : ObjectProperty Cᵒᵖ) : (P ⊓ Q).unop = P.unop ⊓ Q.unop := rfl

end
end CategoryTheory.ObjectProperty
end
