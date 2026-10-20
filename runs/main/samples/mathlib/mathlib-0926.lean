public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

open OrderDual

section

variable [CompleteLattice α] {f g s : ι → α} {a b : α}

@[to_dual]
theorem biSup_prod' {f : β → γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x.1 x.2 = ⨆ (a ∈ s) (b ∈ t), f a b :=
  biSup_prod

end
end
