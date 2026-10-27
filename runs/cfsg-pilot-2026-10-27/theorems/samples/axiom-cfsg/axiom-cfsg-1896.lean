public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm

section Explicit

theorem a7_syl_fix_unique : ∀ x : Fin 7, (∀ a ∈ a7SylList, a x = x) → x = 0 := by
  intro x hx
  have h := a7_syl_fix_check
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  have := h x (List.mem_finRange x)
  rcases this with h1 | h1
  · exfalso
    rw [List.all_eq_false] at h1
    obtain ⟨a, ha, hne⟩ := h1
    exact (by simpa using hne : ¬ a x = x) (hx a ha)
  · exact h1

end Explicit
end CFSG.AGLEmbeddingD2.GN
end
