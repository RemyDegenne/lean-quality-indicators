namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset

open scoped ENNReal NNReal BoundedContinuousFunction

open Finset MeasureTheory Filter Topology

open scoped BigOperators

open Finset Matrix

open scoped Matrix.Norms.L2Operator

open Matrix

namespace SmoothObstruction.EuclideanSplitting

variable {d : ℕ}

lemma opNorm_le_exp (A : Matrix (Fin d) (Fin d) ℝ) {C E : ℝ}
    (hE : 1 ≤ E) (hA : ∀ i j, |A i j| ≤ Real.exp (C*E)) :
    ‖A‖ ≤ Real.exp ((C+(d:ℝ)^2)*E) := by
  have hd : (d:ℝ)^2 ≤ Real.exp ((d:ℝ)^2*E) := by
    calc
      _ ≤ Real.exp ((d:ℝ)^2) := by linarith [Real.add_one_le_exp ((d:ℝ)^2)]
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (sq_nonneg _) hE)
  calc
    _ ≤ (d:ℝ)^2*Real.exp (C*E) := opNorm_le_entry A (Real.exp_nonneg _) hA
    _ ≤ Real.exp ((d:ℝ)^2*E)*Real.exp (C*E) :=
      mul_le_mul_of_nonneg_right hd (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end SmoothObstruction.EuclideanSplitting
end
end OAI
