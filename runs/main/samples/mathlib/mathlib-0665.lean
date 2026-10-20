public section

open Function OrderDual Set

variable {α β : Type*} {ι : Sort*}

open OrderDual

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

@[to_dual iSup_inf_le_sSup_inf ]
theorem sInf_sup_le_iInf_sup : sInf s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_iInf₂ fun _ h => sup_le_sup_right (sInf_le h) _

end CompleteLattice
end
