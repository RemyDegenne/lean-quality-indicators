universe v w

open scoped NatOrdinal HahnSeries

open Berarducci MvPolynomial OrdinalGraded Filter Topology

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

theorem translatedTruncation_C_of_neg (k : K) {γ : ℝ} (hγ : γ < 0) :
    translatedTruncation (HahnSeries.C k : K⟦ℝ⟧) γ = 0 := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation, Subring.coe_zero, HahnSeries.coeff_zero]
  split_ifs with hδ
  · rw [HahnSeries.C_apply, HahnSeries.coeff_single, ite_eq_right (by linarith)]
  · rfl

end Berarducci
end
