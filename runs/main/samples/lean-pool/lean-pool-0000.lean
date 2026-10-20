@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology

open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

theorem exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall
    {g : Point n -> Real} (B : Hessian n) {r : Real}
    (hconv : ConvexOn Real Set.univ g) (hr : 0 <= r) :
    ∃ lambda : Real,
      CoordinateSemiconvexOn lambda (Metric.closedBall (0 : Point n) r)
        (strictifiedQuadraticObjective g B) := by
  let eta : Real := ∑ i : Fin n, ∑ j : Fin n, |B i j|
  have heta : 0 <= eta := by
    exact Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => abs_nonneg (B i j)
  have hB : ∀ i j : Fin n, |B i j| <= eta := by
    intro i j
    calc
      |B i j| <= ∑ j : Fin n, |B i j| := by
        exact Finset.single_le_sum (fun k _hk => abs_nonneg (B i k)) (Finset.mem_univ j)
      _ <= eta := by
        exact Finset.single_le_sum
          (fun k _hk => Finset.sum_nonneg fun l _hl => abs_nonneg (B k l))
          (Finset.mem_univ i)
  exact ⟨eta * (n : Real) * (n : Real) +
      2 * (4 * (n : Real) ^ 2 * r ^ 2 + 2 * (n : Real) * r ^ 2),
    coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall_of_entrywise_abs_le
      (n := n) (B := B) hconv hr heta hB⟩

end ViscositySolns
end
