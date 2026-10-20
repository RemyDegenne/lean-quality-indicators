@[expose] public section

noncomputable section

open ENNReal Set Filter

variable {α β : Type*}

namespace MeasureTheory

namespace Measure

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

theorem bind_apply₀ {m : Measure α} {f : α → Measure β} {s : Set β}
    (hs : NullMeasurableSet s (m.bind f)) (hf : AEMeasurable f m) :
    bind m f s = ∫⁻ a, f a s ∂m := by
  obtain ⟨t, -, ht, hst⟩ := hs.exists_measurable_superset_ae_eq
  rw [← measure_congr hst, bind_apply ht hf]
  exact lintegral_congr_ae <| (ae_ae_of_ae_bind hf hst).mono fun a h ↦ measure_congr h

end Measure
end MeasureTheory
end
end
