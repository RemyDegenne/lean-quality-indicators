namespace P2MW.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero

set_option autoImplicit false

namespace Function

p2m_open

open OrbitPrimitive in

theorem OrbitPrimitive.main {X : Type*} {A : Type*} [AddCommGroup A]
    (f : X → X) (hf : ∀ x : X, 0 < minimalPeriod f x) (v : X → A)
    (hv : ∀ x : X, ∑ k ∈ Finset.range (minimalPeriod f x), v (f^[k] x) = 0) :
    ∃ G : X → A, ∀ x : X, v x = G (f x) - G x := by
  classical
  refine ⟨fun x => ∑ k ∈ Finset.range (idx f hf x), v (f^[k] (base f hf x)), fun x => ?_⟩
  simp only
  rw [base_apply f hf x]
  rcases idx_apply f hf x with ⟨h1, -⟩ | ⟨h0, hm⟩
  · rw [h1, Finset.sum_range_succ, iterate_idx, add_sub_cancel_left]
  · rw [h0, Finset.sum_range_zero, zero_sub]
    have htot := hv (base f hf x)
    rw [← hm, Finset.sum_range_succ, iterate_idx] at htot

    exact (neg_eq_of_add_eq_zero_left htot).symm ▸ (neg_neg _).symm

end Function
end P2MW.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero
