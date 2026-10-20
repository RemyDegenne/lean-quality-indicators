public section

open NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K]

variable [NumberField K]

theorem exists_ne_zero_forall_isReal_pos (s : {w : InfinitePlace K // w.IsReal} → ℝ)
    (hs : ∀ w, s w ≠ 0) :
    ∃ x : K, x ≠ 0 ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < s w * embedding_of_isReal w.2 x := by
  classical
  -- Aim at `1` where the prescribed sign is positive and at `-1` where it is negative.
  obtain ⟨b, habs, hb⟩ := exists_forall_apply_eq_one_and_embedding_of_isReal_eq (K := K)
    fun w => if 0 < s w then 1 else -1
  have hb' : ∀ w : {w : InfinitePlace K // w.IsReal},
      embedding_of_isReal w.2 (b w.1) = if 0 < s w then (1 : ℝ) else -1 := fun w => by
    rw [hb w]
    split_ifs <;> simp
  obtain ⟨x, hx⟩ := exists_forall_infinitePlace_sub_lt b (fun _ => 1) fun _ => one_pos
  have hx0 := ne_zero_of_infinitePlace_sub_lt
    (habs (Classical.arbitrary (InfinitePlace K))) (hx (Classical.arbitrary (InfinitePlace K)))
  refine ⟨x, hx0, fun w => ?_⟩
  have h := mul_pos_of_infinitePlace_sub_lt w.2 (habs w.1) (hx w.1)
  rw [hb' w] at h
  by_cases h' : 0 < s w
  · rw [ite_eq_left h', one_mul] at h
    exact mul_pos h' h
  · rw [ite_eq_right h', neg_one_mul, neg_pos] at h
    exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.mp h') (hs w)) h

end NumberField
end
