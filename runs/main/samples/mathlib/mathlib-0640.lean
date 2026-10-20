@[expose] public section

open OrderDual Set

variable {α β : Type*} {ι : Sort*}

section Preorder

variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

@[to_dual (attr := simp)]
theorem upperClosure_image (f : α ≃o β) :
    upperClosure (f '' s) = UpperSet.map f (upperClosure s) := by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp only [SetLike.mem_coe]
  simp [f.le_symm_apply]

end Preorder
end
