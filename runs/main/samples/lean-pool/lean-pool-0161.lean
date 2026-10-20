@[expose] public section

open scoped BigOperators ENNReal

open Set

open MeasureTheory

namespace Feige

variable {n : ℕ}

theorem exponentialCoordinateBasis_addHaar_eq_volume :
    (exponentialCoordinateBasis (n := n)).addHaar =
      (volume : Measure (ℝ × (Fin n → ℝ))) := by
  classical
  let e : (Option (Fin n) → ℝ) ≃L[ℝ] (ℝ × (Fin n → ℝ)) :=
    (LinearEquiv.piOptionEquivProd ℝ).toContinuousLinearEquiv
  unfold exponentialCoordinateBasis
  change ((Pi.basisFun ℝ (Option (Fin n))).map e.toLinearEquiv).addHaar = _
  rw [← Module.Basis.map_addHaar (Pi.basisFun ℝ (Option (Fin n))) e]
  have hpi : (Pi.basisFun ℝ (Option (Fin n))).addHaar =
      (volume : Measure (Option (Fin n) → ℝ)) := by
    rw [Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [hpi]
  have hg : Measure.map (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin n) ↦ ℝ))
      (volume : Measure (Option (Fin n) → ℝ)) =
      (volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ) := by
    rw [(MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) ↦ ℝ)).map_apply_eq_iff_map_symm_apply_eq]
    simpa only [volume_pi] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Fin n) ↦ (volume : Measure ℝ))).symm
  rw [show (e : (Option (Fin n) → ℝ) → (ℝ × (Fin n → ℝ))) =
      Prod.swap ∘ (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin n) ↦ ℝ)) by rfl]
  rw [← Measure.map_map measurable_swap (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin n) ↦ ℝ)).measurable]
  rw [hg, Measure.prod_swap]
  exact (Measure.volume_eq_prod ℝ (Fin n → ℝ)).symm

end Feige
end
