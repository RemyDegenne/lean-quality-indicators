@[expose] public section

open Set

variable {ι ι' R : Type*} [Ring R] (I J : Ideal R) {a b : R}

namespace Ideal.Quotient

@[simp]
lemma mk_span_range (f : ι → R) [(span (range f)).IsTwoSided] (i : ι) :
    mk (span (.range f)) (f i) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

end Ideal.Quotient
end
