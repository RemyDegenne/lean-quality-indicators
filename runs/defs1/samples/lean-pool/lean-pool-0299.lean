@[expose] public section

namespace LeanPool.CencovPetz

open scoped BigOperators

universe u

namespace MarkovMorphism

variable {α : Type u} [Fintype α]

variable (m : α → ℕ) (hm : ∀ a, 0 < m a)

/-- Fiberwise split: send `a` to the uniform distribution on the fiber `Fin (m a)`. -/
noncomputable def split : MarkovMorphism α (SplitTarget (α := α) m) := by
  classical
  refine
    { K := fun a b => if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro a b
    by_cases h : b.1 = a <;> simp [h]
  · intro a
    have hm_ne : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
    -- Expand the sigma-sum, discard the non-matching fibers, and sum the constant on `Fin (m a)`.
    calc
      (∑ b : SplitTarget (α := α) m, (if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0))
          = ∑ x : α, ∑ _i : Fin (m x), if x = a then (1 : ℝ) / (m a : ℝ) else 0 := by
              simpa [SplitTarget] using
                (Fintype.sum_sigma (f := fun b : SplitTarget (α := α) m =>
                  if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0))
      _ = ∑ _i : Fin (m a), (1 : ℝ) / (m a : ℝ) := by
            -- Only the fiber over `a` contributes.
            simp [eq_comm]
      _ = (m a : ℝ) * ((1 : ℝ) / (m a : ℝ)) := by
            simp_all
      _ = 1 := by
            -- Cancel `m a`.
            field_simp [hm_ne]
  · intro b
    refine ⟨b.1, ?_⟩
    simp_all

end MarkovMorphism
end LeanPool.CencovPetz
end
