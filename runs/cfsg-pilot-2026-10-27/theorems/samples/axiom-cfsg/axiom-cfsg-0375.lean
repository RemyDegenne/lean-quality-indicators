public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Aux

variable {α : Type*} [Fintype α]

theorem cfInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → α → ℂ) (h : α → ℂ) :
    cfInner (∑ i ∈ s, f i) h = ∑ i ∈ s, cfInner (f i) h := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [cfInner_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, cfInner_add_left, ih, Finset.sum_cons]

end Aux
end CFSG.FeitThompson
end
