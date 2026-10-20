@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment

variable {L : Type}

section Relabel

/-- The odd colourings are the same on both sides of a relabel: the
flags and the pairing are untouched. -/
def edgeOddRelabelEquiv {α : Type} {β : Type} {W : Fragment α} (ee : α ≃ β)
    (F : EdgeSubset W) (ℓ : ℕ) :
    (F.relabelUp ee).EdgeOddColouring ℓ ≃ F.EdgeOddColouring ℓ :=
  Equiv.refl _

end Relabel
end EdgeSubset
end RS
end
