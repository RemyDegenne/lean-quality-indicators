@[expose] public section

universe u₁ u₂

namespace Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

namespace Pivot

variable {R} {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) 𝕜)

open Unit Sum TransvectionStruct

theorem listTransvecCol_getElem {i : ℕ} (h : i < (listTransvecCol M).length) :
    (listTransvecCol M)[i] =
      letI i' : Fin r := ⟨i, length_listTransvecCol M ▸ h⟩
      transvection (inl i') (inr unit) <| -M (inl i') (inr unit) / M (inr unit) (inr unit) := by
  simp [listTransvecCol]

end Pivot
end Matrix
end
