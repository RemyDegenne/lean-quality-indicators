public section

open scoped Matrix

variable {l m n ι : Type*}

namespace Matrix

open TauCeti

@[simp]
theorem realify_apply_inr_inl {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inr i) (Sum.inl j) = RCLike.im (A i j) := by simp [realify]

end Matrix
end
