namespace OAI

namespace SiegelZeros

open scoped BigOperators

namespace WeightedTorusJets

variable {K : Type*} [Field K]

theorem biquadraticDirections_linearIndependent [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent K (biquadraticDirections a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_succ, biquadraticDirections] at h0 h1 h2
  have hc0 : c 0 = 0 := by
    apply (mul_eq_zero.mp (show 2 * a * c 0 = 0 by linear_combination a * h0 + h1)).resolve_left
    exact mul_ne_zero two_ne_zero ha
  have hc2 : c 2 = 0 := by
    apply (mul_eq_zero.mp (show 2 * b * c 2 = 0 by linear_combination b * h0 - h2)).resolve_left
    exact mul_ne_zero two_ne_zero hb
  have hc1 : c 1 = 0 := by linear_combination h0 - hc0 - hc2
  fin_cases i <;> assumption

end WeightedTorusJets
end SiegelZeros
end OAI
