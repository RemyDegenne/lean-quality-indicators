@[expose] public section

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open MeasureTheory Set Filter

open scoped InnerProductSpace BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem boundedSelfAdjointBorelCalculusC_congr_on_spectrum'
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {f g : ℝ → ℂ}
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hg : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x ∈ realSpectrum A, f x = g x) :
    boundedSelfAdjointBorelCalculusC A hA f hf hfb =
      boundedSelfAdjointBorelCalculusC A hA g hg hgb := by
  refine TauCeti.BorelCalculus.borelCalculus_congr_ae _ _ _ fun η =>
    Filter.Eventually.of_forall fun w => ?_
  refine hfg _ ?_
  change ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ A
  rw [coe_reCoord A hA w]
  exact w.2

end
end DavisKahanExt
end TauCeti
end
