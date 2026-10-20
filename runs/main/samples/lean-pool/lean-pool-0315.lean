@[expose] public section

open MeasureTheory

namespace V7.Stage7StrictRandomizedExpected

open Stage6StrictDeterministic

attribute [local instance] Classical.propDecidable

theorem hittingTime_gt_of_no_success_before
    (method : StrictLocalMethod) (oracle : PairOracle 1)
    (traces : ℕ → StrictTranscript) (N : ℕ)
    (hfail : ∀ m ≤ N, ¬ StrictSuccessThrough method oracle (traces m) m) :
    (N : ENNReal) < strictHittingTime method oracle traces := by
  unfold strictHittingTime
  rw [lt_sInf_iff]
  refine ⟨((N + 1 : ℕ) : ENNReal), ?_, ?_⟩
  · exact_mod_cast Nat.lt_succ_self N
  intro t ht
  rcases ht with ⟨m, rfl, hsuccess⟩
  have hNm : N < m := by
    by_contra hnot
    exact hfail m (Nat.le_of_not_gt hnot) hsuccess
  have hsucc : N + 1 ≤ m := by omega
  exact_mod_cast hsucc

end V7.Stage7StrictRandomizedExpected
end
