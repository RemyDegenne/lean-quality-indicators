namespace OAI

section

noncomputable section

open scoped BigOperators NNReal ENNReal Topology

open MeasureTheory ProbabilityTheory Filter Set

namespace SKRatio.MatrixNet

open SKRatioClock.Regression

attribute [local instance] Classical.propDecidable

lemma bilinearCoefficient_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    ∑ p, bilinearCoefficient x y p ^ 2 ≤
      2 * (∑ i, x i^2) * (∑ i, y i^2) := by
  have hp (i j : Fin n) : bilinearCoefficient x y (i,j)^2 +
      bilinearCoefficient x y (j,i)^2 ≤ 2 * (x i^2*y j^2 + x j^2*y i^2) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
    · subst j; simp only [bilinearCoefficient, lt_self_iff_false, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      positivity
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [mul_add, Finset.sum_add_distrib] at hs
  rw [Finset.sum_comm (f := fun i j => bilinearCoefficient x y (j,i)^2)] at hs
  rw [Fintype.sum_prod_type]
  have he : ∑ i, ∑ j, 2*(x i^2*y j^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    calc
      _ = 2 * (∑ i, ∑ j, x i^2*y j^2) := by simp only [Finset.mul_sum]
      _ = 2 * ((∑ i, x i^2) * (∑ j, y j^2)) := by rw [Finset.sum_mul_sum]
      _ = _ := by ring
  have he' : ∑ i, ∑ j, 2*(x j^2*y i^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    rw [Finset.sum_comm]; exact he
  rw [he, he'] at hs
  linarith

end SKRatio.MatrixNet
end
end
end OAI
