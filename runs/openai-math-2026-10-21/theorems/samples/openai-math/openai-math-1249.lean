namespace OAI

section

namespace DilutedSpinGlass

open _root_.MeasureTheory _root_.OAI.MeasureTheory

lemma measurePreserving_selectRoot {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (l : ℕ) (b : RootPath Bool l) :
    MeasurePreserving (selectRoot (X := X) l b) (rootLaw l (fun _ => μ))
      (rootLaw (selectedCount l b) (fun _ => μ)) := by
  induction l with
  | zero => exact MeasurePreserving.id _
  | succ l ih =>
    cases b with | mk a b =>
      cases a
      · change MeasurePreserving (fun z : X×RootPath X l => selectRoot l b z.2)
          (μ.prod (rootLaw l (fun _ => μ))) (rootLaw (selectedCount l b) (fun _ => μ))
        exact (ih b).comp (measurePreserving_snd (μ := μ) (ν := rootLaw l (fun _ => μ)))
      · change MeasurePreserving (fun z : X×RootPath X l => (z.1,selectRoot l b z.2))
          (μ.prod (rootLaw l (fun _ => μ))) (μ.prod (rootLaw (selectedCount l b) (fun _ => μ)))
        exact (MeasurePreserving.id μ).prod (ih b)

end DilutedSpinGlass
end
end OAI
