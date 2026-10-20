open scoped Finset

@[expose] public section

open Function Multiset

variable {ι : Type*}

namespace Finset

section Sigma

variable {α : ι → Type*} {β : Type*} (s s₁ s₂ : Finset ι) (t t₁ t₂ : ∀ i, Finset (α i))

variable {s s₁ s₂ t t₁ t₂}

variable (s t) (f : (Σ i, α i) → β)

theorem _root_.biSup_finsetSigma [CompleteLattice β] (s : Finset ι) (t : ∀ i, Finset (α i))
    (f : Sigma α → β) : ⨆ ij ∈ s.sigma t, f ij = ⨆ (i ∈ s) (j ∈ t i), f ⟨i, j⟩ := by
  simp_rw [← Finset.iSup_coe, Finset.coe_sigma, biSup_sigma]

end Sigma
end Finset
end
