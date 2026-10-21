namespace OAI

noncomputable section

open Set MeasureTheory

open scoped BigOperators ENNReal

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem squareSum_mean (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    (hwidth : P.topLength ≤ g.width) {B : ℝ} (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    |integralAverage g.lineMeasure P.squareSum| ≤ squareMeanConstant B := by
  have hmass : g.lineMeasure.real univ = g.width := by
    change (volume.restrict g.root).real univ = g.width
    simpa only [g.cell_zero, FiniteLineGrid.meshWidth, pow_zero, div_one] using g.cell_mass 0 0
  have hnonneg : 0 ≤ ∫ x, P.squareSum x ∂g.lineMeasure := integral_nonneg P.squareSum_nonneg
  rw [integralAverage, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
    abs_of_nonneg hnonneg, hmass]
  calc
    _ ≤ g.width⁻¹ * (squareMeanConstant B * g.width) :=
      mul_le_mul_of_nonneg_left (P.squareSum_root_integral g hwidth hB hbudget)
        (inv_nonneg.mpr g.width_pos.le)
    _ = _ := by field_simp [g.width_pos.ne']

end LipschitzHilbert.LinePacketFamily
end
end OAI
