namespace OAI

namespace Balanced.OccupancyVisibility

open MeasureTheory

theorem visible_excess_of_common_sign
    (P : Profile) (νD νC : Measure Profile)
    [IsFiniteMeasure νD] [IsFiniteMeasure νC]
    {k c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    (hmassD : νD.real Set.univ = k) (hmassC : νC.real Set.univ = c)
    (hincD : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hmean : HasSum (fun ij : ℕ × ℕ => (ij.2 : ℝ) * P ij) c)
    (hP : HasSum (fun j : ℕ => P (0, j)) (Real.exp (-k)))
    (hf : Integrable (fun x : Profile => ∑' j : ℕ, x (0, j)) νC)
    (hincC : (∫ x : Profile, ∑' j : ℕ, x (0, j) ∂νC) =
      ∑' j : ℕ, (j : ℝ) * P (0, j))
    (hdev : (∀ᵐ x : Profile ∂νC, Real.exp (-k) + lam ≤ ∑' j : ℕ, x (0, j)) ∨
      (∀ᵐ x : Profile ∂νC, (∑' j : ℕ, x (0, j)) ≤ Real.exp (-k) - lam)) :
    c < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  have habs : ∀ᵐ x : Profile ∂νC,
      lam ≤ |(∑' j : ℕ, x (0, j)) - Real.exp (-k)| := by
    rcases hdev with hhigh | hlow
    · filter_upwards [hhigh] with x hx
      exact le_trans (by linarith) (le_abs_self _)
    · filter_upwards [hlow] with x hx
      exact le_trans (by linarith) (neg_le_abs _)
  rw [ProfileVisibility.coverVisible_full_of_row_deviation P νC hlam
    hP.summable hP.tsum_eq habs, hmassC]
  linarith [deletionVisible_pos_of_common_sign P νD νC hc hlam hmassD hmassC
    hincD hmean hf hincC hdev]

end Balanced.OccupancyVisibility
end OAI
