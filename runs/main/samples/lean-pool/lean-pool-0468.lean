@[expose] public section

namespace GenLimit.FiniteWitness.Simplified

theorem executableRun_eq {F : List ℕ → ℕ} (hF : Fresh F) {S : Finset ℕ}
    (hS : S.Nonempty) (k : ℕ) : executableRun F S k = sampleRun naturalCheckpoints F S k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
      have hex := candidate_exists naturalCheckpoints hF hS k
      rw [executableRun, ih, sampleRun, dite_eq_left hex]
      exact pick_candidate_eq hF hS (sampleRun_content naturalCheckpoints F S k) k hex

end GenLimit.FiniteWitness.Simplified
end
