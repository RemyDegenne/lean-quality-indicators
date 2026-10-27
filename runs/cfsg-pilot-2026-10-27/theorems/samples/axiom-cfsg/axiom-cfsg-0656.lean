public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule Subgroup

open scoped commutatorElement

theorem exists_dual_apply_eq_zero_of_three_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (hE : 3 ≤ finrank (ZMod 2) E) (a b : E) :
    ∃ (f : Dual (ZMod 2) E) (x : E), f a = 0 ∧ f b = 0 ∧ f x = 1 := by
  obtain ⟨x, -, hx⟩ := exists_mem_notMem_of_finrank_lt (U := ⊤) (S := span (ZMod 2) {a, b})
    (by rw [finrank_top]; have := finrank_span_pair_le a b; omega)
  obtain ⟨f, hf, hfx⟩ := exists_dual_eq_one_of_notMem hx
  exact ⟨f, x, hf a (subset_span (by simp)), hf b (subset_span (by simp)), hfx⟩

end CFSG.GroupTheory.GLnTwoSplitting
end
