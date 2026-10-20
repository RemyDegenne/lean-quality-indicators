namespace P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq

set_option autoImplicit false

open MeasureTheory

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace KcHaarQuotientMulRight

variable {G : Type*} [Group G]

theorem lintegral_density_mul_comp_mul_right_eq [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (h : G)
    (hμh : Measure.map (fun g : G => g * h) μ = μ) :
    ∫⁻ g, HaarQuotient.density H μH g * f (g * h) ∂μ = ∫⁻ g, HaarQuotient.density H μH g * f g ∂μ := by
  set D := HaarQuotient.density H μH with hDdef
  have hD : Measurable D := measurable_density H μH
  have hinv : ∀ (x : H) (g : G), f ((x : G) * g) = f g := fun x g => hfH x x.2 g

  let ρ : G → ℝ≥0∞ := fun g => D (g * h⁻¹)
  have hρ : Measurable ρ := hD.comp (measurable_mul_const _)
  have hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1 := by
    intro g
    show ∫⁻ x : H, D ((x : G) * g * h⁻¹) ∂μH = 1
    simp_rw [mul_assoc]
    exact HaarQuotient.lintegral_density_mul_eq_one H hH μH (g * h⁻¹)

  have h1 : ∫⁻ g, D g * f (g * h) ∂μ = ∫⁻ g, (fun g' => ρ g' * f g') (g * h) ∂μ := by
    refine lintegral_congr fun g => ?_
    show D g * f (g * h) = D (g * h * h⁻¹) * f (g * h)
    rw [mul_inv_cancel_right]
  have h2 : ∫⁻ g, (fun g' => ρ g' * f g') (g * h) ∂μ = ∫⁻ g, ρ g * f g ∂(Measure.map (fun g : G => g * h) μ) :=
    (lintegral_map (hρ.mul hf) (measurable_mul_const h)).symm
  have h3 : ∫⁻ g, ρ g * f g ∂(Measure.map (fun g : G => g * h) μ) = ∫⁻ g, ρ g * f g ∂μ := by
    rw [hμh]
  have h4 : ∫⁻ g, ρ g * f g ∂μ = ∫⁻ g, f g ∂(μ.withDensity ρ) := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hρ hf]
    rfl
  have h5 : ∫⁻ g, f g ∂(μ.withDensity D) = ∫⁻ g, D g * f g ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hD hf]
    rfl
  rw [h1, h2, h3, h4, ← lintegral_withDensity_eq_of_admissible μ H hH μH ρ hρ hρc f hf hinv, h5]

end KcHaarQuotientMulRight
end
end P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
