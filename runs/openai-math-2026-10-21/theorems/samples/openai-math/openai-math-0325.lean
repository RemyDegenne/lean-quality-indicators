namespace OAI

namespace EditApproximation

open Finset

theorem finiteRationalOptimizer_eq_iterate {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) :
    finiteRationalOptimizer coordinates vertices linear G j =
      rationalOptimizerIterate (vertices.headD (fun _ => 0))
        (finiteOptimizerSelection coordinates vertices linear G) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext i
    simp only [finiteRationalOptimizer, rationalOptimizerIterate]
    change (1 - 2 / ((j : ℚ) + 2)) * finiteRationalOptimizer coordinates vertices linear G j i +
        2 / ((j : ℚ) + 2) * finiteOptimizerSelection coordinates vertices linear G j i = _
    rw [ih]

end EditApproximation
end OAI
