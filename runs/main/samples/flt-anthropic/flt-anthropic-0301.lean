namespace P2MW.S_Multiset_filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq

set_option autoImplicit false

namespace P2mRigid

open Finsupp

attribute [local instance] instCoeFunGA instCoeFunAMA

section StageC

open AddMonoidAlgebra

theorem F_apply_eq_neg_count (u : Multiset ℝ) (hu : ∀ w ∈ u, 0 < w) (v : ℝ) (hv0 : 0 < v)
    (hv : ∀ w ∈ u, v ≤ w) : F u v = -(u.count v : ℂ) := by
  classical
  induction u using Multiset.induction with
  | empty =>
    rw [F_zero, one_apply_of_ne hv0.ne', Multiset.count_zero, Nat.cast_zero, neg_zero]
  | cons w u ih =>
    have hu' : ∀ x ∈ u, 0 < x := fun x hx => hu x (Multiset.mem_cons_of_mem hx)
    have hv' : ∀ x ∈ u, v ≤ x := fun x hx => hv x (Multiset.mem_cons_of_mem hx)
    have hvw : v ≤ w := hv w (Multiset.mem_cons_self w u)
    rw [F_cons_apply, ih hu' hv', Multiset.count_cons]
    rcases hvw.lt_or_eq with hlt | heq
    · rw [F_apply_of_neg u hu' (by linarith), if_neg hlt.ne]
      simp
    · subst heq
      rw [sub_self, F_apply_zero u hu', if_pos rfl]
      push_cast
      ring

end StageC
end P2mRigid
end P2MW.S_Multiset_filter_ne_zero_eq_of_forall_prod_one_sub_pow_eq
