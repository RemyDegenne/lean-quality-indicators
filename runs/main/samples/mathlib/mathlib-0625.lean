@[expose] public section

open Set Function MeasureTheory

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}

section Pi

variable {X : δ → Type*} [MeasurableSpace α]

variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]

@[fun_prop]
theorem Finset.measurable_restrict₂_apply {s t : Finset α} (hst : s ⊆ t)
    {f : t → γ} (hf : Measurable f) :
    Measurable (restrict₂ (π := fun _ ↦ γ) hst f) := hf.comp (measurable_inclusion hst)

end Pi
end
