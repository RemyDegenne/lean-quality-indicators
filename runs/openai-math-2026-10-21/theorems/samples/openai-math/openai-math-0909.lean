namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

lemma commonTimes_span {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) :
    P.1 (commonTimes ℓ P (n+1)).1 =
      P.1 (commonTimes ℓ P n).1 + wordPath 0 (commonWords ℓ P n).1 (commonWords ℓ P n).1.length ∧
    P.2 (commonTimes ℓ P (n+1)).2 =
      P.2 (commonTimes ℓ P n).2 + wordPath 0 (commonWords ℓ P n).2 (commonWords ℓ P n).2.length := by
  have he := iterate_renewPairSuffix_eq ℓ P h0 h0' n
  have h1 := (hP n).2.1.1 _ le_rfl
  have h2 := (hP n).2.1.2 _ le_rfl
  rw [he] at h1 h2
  rw [commonTimes_succ]
  constructor
  · exact (sub_eq_iff_eq_add.mp h1).trans (add_comm _ _)
  · exact (sub_eq_iff_eq_add.mp h2).trans (add_comm _ _)

end DirectionalTransience
end
end
end OAI
