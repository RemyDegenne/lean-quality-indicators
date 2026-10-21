namespace OAI

section

namespace BinaryMatching.Algorithm

noncomputable section

open Finset MatchingEntropy

lemma point_succ (G : Input) (hn : 2 ≤ G.n) (j : ℕ) (e : Pair G.n) :
    point G (j+1) e = min 1 (max 0 (point G j e+
      (gradient G (iterate G j).numerators (activeRow (D₀ G) (iterate G j).numerators) e:ℝ)/(D₀ G:ℝ))) := by
  have hD : (0:ℝ) < D₀ G := by exact_mod_cast D₀_pos G hn
  simp only [point, iterate, step, coordinates_cast, update, at_toTable,
    Int.cast_min, Int.cast_max, Int.cast_natCast, Int.cast_zero, Int.cast_add]
  rw [← min_div_div_right hD.le, ← max_div_div_right hD.le]
  rw [div_self hD.ne', zero_div, add_div]

end
end BinaryMatching.Algorithm
end
end OAI
