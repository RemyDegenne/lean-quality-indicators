namespace OAI

section

section

noncomputable section

open Set

open scoped Classical

namespace SimpleGraph.Walk

open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk

variable {V : Type*} {H : SimpleGraph V}

lemma exists_first_crossing (f : V → ℝ) (ρ T : ℝ)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y| ≤ ρ)
    {a b : V} (w : H.Walk a b) (ha : f a < T) (hb : T ≤ f b) :
    ∃ x∈w.support, T ≤ f x ∧ f x ≤ T+ρ := by
  induction w with
  | nil =>  exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T ≤ f c
    · refine ⟨c,?_,hc,?_⟩
      · simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]
        exact Or.inr w.start_mem_support
      · have hh := hf hac
        rw [abs_le] at hh
        linarith
    · obtain ⟨x,hx,h1,h2⟩ := ih (lt_of_not_ge hc) hb
      exact ⟨x,by simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx,h1,h2⟩

end SimpleGraph.Walk
end
end
end
end OAI
