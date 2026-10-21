namespace OAI

noncomputable section

open scoped BigOperators

open MeasureTheory intervalIntegral

open Finset

open Finset Nat ArithmeticFunction

open scoped ArithmeticFunction.Moebius

open Filter

open MeasureTheory Filter

open MeasureTheory

open MeasureTheory Set

open Set MeasureTheory Complex

open Set

open Finset Filter

open ArithmeticFunction

open MeasureTheory Finset

open Classical

namespace OrdinaryCorrelations.FiniteResidues

theorem cube_boundary (d a N : ℕ) [NeZero d] (hN : 0 < N)
    (F : ZMod d → ZMod d → ZMod d → ℝ) (hF : ∀ x y z, |F x y z| ≤ 1) :
    |cubeMean d a N F - uniformCubeMean d F| ≤ 3*(d:ℝ)/N := by
  rw [cubeMean_eq]
  have he : (∑ x, ∑ y, ∑ z, mass d a N x * mass d a N y * mass d a N z * F x y z) -
      uniformCubeMean d F = ∑ x, ∑ y, ∑ z,
      (mass d a N x * mass d a N y * mass d a N z - (d:ℝ)⁻¹^3)*F x y z := by
    unfold uniformCubeMean
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib,sub_mul]
  rw [he]
  calc
    _ ≤ ∑ x, |∑ y, ∑ z, (mass d a N x*mass d a N y*mass d a N z-(d:ℝ)⁻¹^3)*F x y z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, ∑ z, |(mass d a N x*mass d a N y*mass d a N z-(d:ℝ)⁻¹^3)*F x y z| := by
      apply Finset.sum_le_sum
      intro x _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun y _ =>
        Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ x, ∑ y, ∑ z, |mass d a N x*mass d a N y*mass d a N z-(d:ℝ)⁻¹^3| := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF x y z)
    _ ≤ _ := product_mass_discrepancy d a N hN

end OrdinaryCorrelations.FiniteResidues
end
end OAI
