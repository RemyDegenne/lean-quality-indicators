@[expose] public section

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Set Filter Relator

section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsMinOn.sup (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊔ g x) s a :=
  IsMinFilter.sup hf hg

end SemilatticeSup
end
