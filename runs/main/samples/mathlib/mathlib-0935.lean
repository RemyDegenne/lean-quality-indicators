@[expose] public section

noncomputable section

open Set Function MeasurableSpace Filter ENNReal

open Filter hiding map

variable {α β δ : Type*} {ι : Sort*}

notation3 "∀ᵐ "(...)", "r:(scoped P =>
  Filter.Eventually P <| MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

notation3 "∃ᵐ "(...)", "r:(scoped P =>
  Filter.Frequently P <| MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

macro "volume_tac" : tactic =>
  `(tactic| exact MeasureTheory.MeasureSpace.volume)

section

open MeasureTheory

variable {m : MeasurableSpace α} [MeasurableSpace β] {f g : α → β} {μ : Measure α}

scoped[MeasureTheory] notation "AEMeasurable[" m "]" => @AEMeasurable _ _ _ m

@[fun_prop]
theorem aemeasurable_id' : AEMeasurable (fun x => x) μ :=
  measurable_id.aemeasurable

end
end
end
