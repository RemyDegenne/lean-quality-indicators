public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

open OrderDual

section SupSet

variable [SupSet α] {f g : ι → α}

@[to_dual]
theorem sSup_range : sSup (range f) = iSup f :=
  rfl

end SupSet
end
