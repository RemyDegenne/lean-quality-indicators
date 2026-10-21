namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pderiv_booleanCoefficient {α ι : Type*} [DecidableEq α]
    (j : ι) (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) :
    MvPolynomial.pderiv j (booleanCoefficient f s) =
      booleanCoefficient (fun t => MvPolynomial.pderiv j (f t)) s := by
  classical
  unfold booleanCoefficient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc, MvPolynomial.pderiv_C_mul]

end Erdos3
end
end OAI
