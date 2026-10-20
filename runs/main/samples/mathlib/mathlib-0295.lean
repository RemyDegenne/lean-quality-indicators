@[expose] public section

namespace Matrix

section CommSemiring

variable {m n R : Type*} [CommSemiring R] {M : Matrix m n R}

lemma separatingRight_def [Fintype m] [Fintype n] :
    M.SeparatingRight ↔ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  refine forall_congr' fun w ↦ ⟨fun hM hw ↦ hM ?_, fun hM hw ↦ hM ?_⟩ <;>
  convert hw

end CommSemiring
end Matrix
end
