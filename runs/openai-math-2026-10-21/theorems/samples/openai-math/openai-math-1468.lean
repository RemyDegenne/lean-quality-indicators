namespace OAI

section

noncomputable section

open MeasureTheory Set

open scoped FourierTransform RealInnerProductSpace

namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] dampedLineResolvent

theorem fourier_dampedLine_integral {f : FourierSpace → ℂ} (hf : Integrable f)
    (w k : FourierSpace) :
    𝓕 (dampedLineResolvent f w) k =
      ∫ s in Ioi (0 : ℝ), Real.exp (-s) • 𝓕 (fun x => f (x-s • w)) k := by
  rw [Real.fourier_eq]
  calc
    _ = ∫ x : FourierSpace, ∫ s in Ioi (0 : ℝ), fourierLineKernel f w k (s,x) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change 𝐞 (-inner ℝ x k) • dampedLineResolvent f w x = _
        unfold dampedLineResolvent
        change ((𝐞 (-inner ℝ x k) : ℂ) *
          ∫ s in Ioi (0 : ℝ), Real.exp (-s) • f (x-s • w)) = _
        rw [← integral_const_mul]
        rfl)
    _ = ∫ s in Ioi (0 : ℝ), ∫ x : FourierSpace, fourierLineKernel f w k (s,x) :=
      (integral_integral_swap (f := fun s x => fourierLineKernel f w k (s,x))
        (fourierLineKernel_integrable hf w k)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun s => by
        change (∫ x : FourierSpace, fourierLineKernel f w k (s,x)) =
          Real.exp (-s) • 𝓕 (fun x => f (x-s • w)) k
        rw [Real.fourier_eq,← integral_smul]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by
          exact smul_comm (𝐞 (-inner ℝ x k)) (Real.exp (-s)) (f (x-s • w))))

end BoltzmannNonuniqueness.Published
end
end
end OAI
