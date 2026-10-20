@[expose] public section

variable {α : Type*}

namespace Ordnode

@[simp]
theorem merge_nil_left (t : Ordnode α) : merge t nil = t := by cases t <;> rfl

end Ordnode
end
