@[expose] public section

open Finset

namespace Zeta5Irrational

lemma cov_434_437 :
    ∀ t,
      (1837116607039 / 4000000000000 : ℝ) ≤ t →
        t ≤ (922531203149 / 2000000000000 : ℝ) → 0 < t → 2 * Uρ t - Vfield t ≤ M0 :=
  fun t h1 h2 h0 =>
  (le_or_gt t (229970650849 / 500000000000 : ℝ)).elim (fun h => tc_434 t h1 h h0)
    (fun h => cov_435_437 t h.le h2 h0)

end Zeta5Irrational
end
