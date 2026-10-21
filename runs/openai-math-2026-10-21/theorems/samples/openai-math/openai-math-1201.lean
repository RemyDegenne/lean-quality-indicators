namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

lemma commonTrueRecord_congr_prefix {d : ℕ} (ℓ : Vector d)
    {P Q : Path d × Path d} {j k n m : ℕ}
    (hP : ∀ i ≤ n, P.1 i = Q.1 i) (hQ : ∀ i ≤ m, P.2 i = Q.2 i)
    (hj : j ≤ n) (hk : k ≤ m) :
    (StrictRecord ℓ P.1 j ∧ StrictRecord ℓ P.2 k ∧
        dot (realPosition (P.1 j)) ℓ = dot (realPosition (P.2 k)) ℓ) ↔
      (StrictRecord ℓ Q.1 j ∧ StrictRecord ℓ Q.2 k ∧
        dot (realPosition (Q.1 j)) ℓ = dot (realPosition (Q.2 k)) ℓ) := by
  rw [strictRecord_congr_prefix ℓ hj hP, strictRecord_congr_prefix ℓ hk hQ,
    hP j hj, hQ k hk]

end DirectionalTransience
end
end
end OAI
