@[expose] public section

open Int

namespace Rat

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

variable {R : Type*} [Ring R] [LinearOrder R] [FloorRing R]

section NormNum

open Mathlib.Meta.NormNum Qq

theorem isInt_round (r : R) (m : ℤ) : IsInt r m → IsInt (round r) m := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

end NormNum
end Rat
end
