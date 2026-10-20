public section

variable {α β : Type*} {f : α → β}

open Set

namespace Set

variable [Preorder α] {p : α → Prop}

@[to_dual existing (attr := simp)]
lemma image_subtype_val_Ioc_Iic {a b : α} (c : Ioc a b) : Subtype.val '' Iic c = Ioc a c :=
  image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

end Set
end
