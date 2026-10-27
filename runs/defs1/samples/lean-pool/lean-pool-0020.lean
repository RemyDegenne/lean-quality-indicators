@[expose] public section

namespace RS

/-- **The paired step, value form**: across a π-returning
repair block, canonical-orientation existence transfers and the
pairing-resolved signed value is preserved. -/
def PairedValueLedger : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ₁ κ₂ : F.RelTransitionSystem),
    EdgeSubset.PairedStep κ₁ κ₂ →
    Nonempty {o : κ₁.Orientation // EdgeSubset.PathCanonical o} →
    Nonempty {o : κ₂.Orientation // EdgeSubset.PathCanonical o} ∧
      F.signedValueAt hM st hbnd κ₁ = F.signedValueAt hM st hbnd κ₂

end RS
end
