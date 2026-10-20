@[expose] public section

open scoped BigOperators

namespace Feige

namespace CalibratedChain

variable {m : ℕ} (C : CalibratedChain m)

theorem sum_chainMass_shift (K : ℕ → ℝ) (t r : ℕ) :
    (∑ j ∈ Finset.range r, chainMass K (t + j)) = K t - K (t + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [chainMass]
      ring_nf

end CalibratedChain
end Feige
end
