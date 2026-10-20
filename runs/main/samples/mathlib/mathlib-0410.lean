@[expose] public section

namespace Matrix

variable {α β m n : Type*} {A : Matrix n n α}

section AddMonoid

variable [AddMonoid α] [StarAddMonoid α]

theorem isHermitian_blockDiagonal'_iff [DecidableEq n] {p : n → Type*}
    {M : ∀ i, Matrix (p i) (p i) α} : (blockDiagonal' M).IsHermitian ↔ ∀ i, (M i).IsHermitian := by
  grind [IsHermitian, blockDiagonal'_conjTranspose, blockDiagonal'_inj]

end AddMonoid
end Matrix
end
