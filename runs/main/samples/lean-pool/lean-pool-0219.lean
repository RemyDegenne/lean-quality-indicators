@[expose] public section

open Finset

namespace Zeta5Irrational

lemma cov_302_304 :
    ∀ t,
      (723732917263 / 2560000000000 : ℝ) ≤ t →
        t ≤ (36419876534909 / 128000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  fun t h1 h2 h0 =>
  (le_or_gt t (4542766622207 / 16000000000000 : ℝ)).elim (fun h => tc_302 t h1 h h0)
    (fun h => tc_303 t h.le h2 h0)

end Zeta5Irrational
end
