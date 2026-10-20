@[expose] public section

variable {α β : Type*}

namespace Set

section Einfsep

open ENNReal

open Function

section EDist

variable [EDist α] {x y : α} {s t : Set α}

theorem le_einfsep_iff {d} :
    d ≤ s.einfsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y := by
  simp_rw [einfsep, le_iInf_iff]

end EDist
end Einfsep
end Set
end
