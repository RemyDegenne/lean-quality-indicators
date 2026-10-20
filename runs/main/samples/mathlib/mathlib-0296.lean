public section

namespace Int

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

namespace ModEq

theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [ZMOD n]) : (l.map f).sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map h

end ModEq
end Int
end
