@[expose] public section

noncomputable section

open MeasureTheory Homogenization

open scoped Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section4

theorem TemperatureError.temperature_spaceGrad_finset_sum {ι : Type*}
    (s : Finset ι) (u : ι → ℝ → Vec 2 → ℝ)
    (hD : ∀ i ∈ s, ∀ t, 0 < t → Differentiable ℝ (u i t))
    (t : ℝ) (ht : 0 < t) (x : Vec 2) :
    spaceGrad (fun y => ∑ i ∈ s, u i t y) x =
      ∑ i ∈ s, spaceGrad (u i t) x := by
  classical
  funext j
  change fderiv ℝ (fun y => ∑ i ∈ s, u i t y) x (basisVec j) = _
  have hAt : ∀ i ∈ s, DifferentiableAt ℝ (fun y => u i t y) x := by
    intro i hi
    exact hD i hi t ht x
  have hsumfun : (fun y => ∑ i ∈ s, u i t y) = ∑ i ∈ s, fun y => u i t y := by
    funext y
    simp only [Finset.sum_apply]
  rw [hsumfun, fderiv_sum hAt]
  simp [spaceGrad]

end AVenhance.Infra.Section5.RelativeError
end
end
