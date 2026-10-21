namespace OAI

section

namespace DilutedSpinGlass

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory

open scoped BigOperators

lemma disorderAverage_map_eq {p : ℕ} (M : Model p)
    (T : InteractionSample p → InteractionSample p) (g : ℝ → ℝ)
    (hT : Measurable T) (hg : Measurable g) (N k : ℕ) :
    disorderAverage (mapModel M T g hT hg) N k=
      ∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (mapModel M T g hT hg) (fun j => T (θ j))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  change (∫ θ : Fin k → InteractionSample p,fieldAverage (N := N) (mapModel M T g hT hg) θ
    ∂Measure.pi (fun _ : Fin k => Measure.map T M.disorder.toMeasure))=_
  exact integral_pi_map _ T hT _ (stronglyMeasurable_fieldAverage (mapModel M T g hT hg) N k).measurable

end DilutedSpinGlass
end
end OAI
