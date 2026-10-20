@[expose] public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Set Filter Relator

section Preorder

variable [Preorder β] [Preorder γ]

variable (f : α → β) (s : Set α) (l : Filter α) (a : α)

variable {f s a l} {t : Set α} {l' : Filter α}

open OrderDual (toDual)

theorem IsMinFilter.filter_mono (h : IsMinFilter f l a) (hl : l' ≤ l) : IsMinFilter f l' a :=
  hl h

end Preorder
end
