@[expose] public section

open Function Set

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

namespace Equiv

variable {α β : Type*}

/-- If `α` is equivalent to `β`, then `Set α` is equivalent to `Set β`.

See also `Equiv.finsetCongr`. -/
@[simps]
def setCongr {α β : Type*} (e : α ≃ β) : Set α ≃ Set β :=
  ⟨fun s => e '' s, fun t => e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

end Equiv
end
