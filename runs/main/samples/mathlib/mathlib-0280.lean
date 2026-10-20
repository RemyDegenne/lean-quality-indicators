@[expose] public section

noncomputable section

open Set

open scoped ComplexConjugate

namespace Complex

variable {z : ℂ}

lemma one_lt_normSq_iff {x : ℂ} : 1 < normSq x ↔ 1 < ‖x‖ := by
  rw [← one_lt_sq_iff₀ (norm_nonneg _), normSq_eq_norm_sq]

end Complex
end
end
