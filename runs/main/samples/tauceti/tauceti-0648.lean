public section

open Polynomial IntermediateField

namespace TauCeti

universe u

variable {F : Type u} [Field F] {f : F[X]} {j : TransitiveGroupIndex 5}

theorem HasGaloisLabel.isSquare_discr_iff_five (h : HasGaloisLabel f j) (hf : f.Monic)
    (hchar : ringChar F ≠ 2) :
    IsSquare f.discr ↔ (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 3 := by
  rw [h.isSquare_discr_iff hf hchar, referenceSubgroup_five_le_alternatingGroup_iff]

end TauCeti
end
