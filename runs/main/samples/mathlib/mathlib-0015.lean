@[expose] public section

open Finset

namespace Nat

variable (p : ℕ → Prop)

variable {p}

lemma nth_mem_anti {a b : ℕ} (hab : a ≤ b) (h : p (nth p b)) : p (nth p a) := by
  by_cases h' : ∀ hf : (Set.ofPred p).Finite, a < #hf.toFinset
  · exact nth_mem a h'
  · simp only [not_forall, not_lt] at h'
    have h'b : ∃ hf : (Set.ofPred p).Finite, #hf.toFinset ≤ b := by
      rcases h' with ⟨hf, ha⟩
      exact ⟨hf, ha.trans hab⟩
    have ha0 : nth p a = 0 := by simp [nth_eq_zero, h']
    have hb0 : nth p b = 0 := by simp [nth_eq_zero, h'b]
    rw [ha0]
    rwa [hb0] at h

end Nat
end
