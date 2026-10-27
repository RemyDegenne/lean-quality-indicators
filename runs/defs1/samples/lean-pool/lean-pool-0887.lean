@[expose] public section

namespace LeanPool.DemazureProduct

namespace ASP321a

section fixed_321a

variable {τ : AspPerm} (h_321a : is321a τ)

include h_321a

section fixed_321a_and_lel

variable {β : AspPerm} (h_L : β ≤L τ)

include h_L

/-- Compatibility of `between_inv_prop` under a left weak-order comparison. -/
structure between_inv_lel_prop (β τ : AspPerm) (u x v : ℤ) where
  /-- The pattern for the larger permutation. -/
  propτ : between_inv_prop (τ := τ) u x v
  /-- The pattern for the smaller permutation. -/
  propβ : between_inv_prop (τ := β) u x v
  /-- Left inversion membership agrees in both permutations. -/
  inv_iff_left : ⟨u, x⟩ ∈ invSet β ↔ ⟨u, x⟩ ∈ invSet τ
  /-- Right inversion membership agrees in both permutations. -/
  inv_iff_right : ⟨x, v⟩ ∈ invSet β ↔ ⟨x, v⟩ ∈ invSet τ
  src_iff : isSrc β x ↔ isSrc τ x
  snk_iff : isSnk β x ↔ isSnk τ x

end fixed_321a_and_lel
end fixed_321a
end ASP321a
end LeanPool.DemazureProduct
end
