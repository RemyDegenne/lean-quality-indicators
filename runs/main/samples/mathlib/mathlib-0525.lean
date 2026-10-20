@[expose] public section

open Function Set Order

open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

section EventuallyEq

variable {l : Filter α} {f g : α → β}

namespace EventuallyEqSet

variable {s t u : Set α} {l l' : Filter α}

@[gcongr]
protected lemma symmDiff (h : s =ᶠ[l] t) {s' t' : Set α} (h' : s' =ᶠ[l] t') :
    s ∆ s' =ᶠ[l] t ∆ t' :=
  (h.diff h').union (h'.diff h)

end EventuallyEqSet
end EventuallyEq
end Filter
end
