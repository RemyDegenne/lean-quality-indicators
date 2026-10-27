@[expose] public section

open Function OrderDual Set

universe u v w x

variable {α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*} {a₁ a₂ : α} {b₁ b₂ : β}

/-- `toDual ∘ Ici` and `sInf ∘ ofDual` form a Galois coinsertion. -/
def gciIciSInf [CompleteSemilatticeInf α] :
    GaloisCoinsertion (toDual ∘ Ici : α → (Set α)ᵒᵈ) (sInf ∘ ofDual : (Set α)ᵒᵈ → α) :=
  gc_Ici_sInf.toGaloisCoinsertion fun _ ↦ sInf_le le_rfl

end
