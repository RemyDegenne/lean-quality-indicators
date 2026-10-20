@[expose] public section

open Function Set Order

open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

section EventuallyEq

variable {l : Filter α} {f g : α → β}

@[gcongr]
theorem EventuallyEq.inf [Min β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : f ⊓ g =ᶠ[l] f' ⊓ g' :=
  hf.comp₂ (· ⊓ ·) hg

end EventuallyEq
end Filter
end
