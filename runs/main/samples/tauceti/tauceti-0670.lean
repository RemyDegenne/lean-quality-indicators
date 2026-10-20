public section

open Function MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

open ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]

section FinArrow

variable {β : Type*} [MeasurableSpace β]

theorem measurePreserving_finFourArrow (μ : Measure β) [SigmaFinite μ] :
    MeasurePreserving (finFourArrow (β := β)) (Measure.pi fun _ : Fin 4 => μ)
      (μ.prod (μ.prod (μ.prod μ))) :=
  ((MeasurePreserving.id μ).prod (measurePreserving_finThreeArrow μ)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 4 => μ) 0)

end FinArrow
end TauCeti
end
