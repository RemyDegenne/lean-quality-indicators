@[expose] public section

namespace MonoidHom

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

@[to_additive]
lemma fst_mono : Monotone (MonoidHom.fst α β) :=
  fun _ _ ↦ by simp +contextual [Prod.le_def]

end MonoidHom
end
