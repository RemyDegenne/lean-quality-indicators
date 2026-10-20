@[expose] public section

open Function Set Order

open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

section EventuallyEq

variable {l : Filter α} {f g : α → β}

section Preorder

variable [Preorder β] {l : Filter α} {f g h : α → β}

theorem EventuallyLE.rfl : f ≤ᶠ[l] f :=
  EventuallyLE.refl l f

end Preorder
end EventuallyEq
end Filter
end
