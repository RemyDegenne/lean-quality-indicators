@[expose] public section

open Set Function MeasureTheory

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}

section Atoms

variable [MeasurableSpace β]

lemma measurableAtom_subset {s : Set β} {x : β} (hs : MeasurableSet s) (hx : x ∈ s) :
    measurableAtom x ⊆ s :=
  iInter₂_subset_of_subset s hx fun ⦃a⦄ ↦ (by simp [hs])

end Atoms
end
