@[expose] public section

namespace Matrix

variable {R : Type*}

variable {m m₁ m₂ n n₁ n₂ : Type*}

section Semiring

variable [Semiring R]

lemma fromBlocks_mul_fromRows [Fintype n₁] [Fintype n₂] (A₁ : Matrix n₁ n R) (A₂ : Matrix n₂ n R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ * (fromRows A₁ A₂) =
      fromRows (B₁₁ * A₁ + B₁₂ * A₂) (B₂₁ * A₁ + B₂₂ * A₂) := by
  ext (_ | _) _ <;> simp [mul_apply]

end Semiring
end Matrix
end
