@[expose] public section

universe u v w

namespace Module

section AddCommMonoid

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- `IsKilledByIdealPower R M I` means that one power of `I` annihilates the
whole module `M`. -/
def IsKilledByIdealPower (I : Ideal R) : Prop :=
  ∃ n : ℕ, Module.IsTorsionBySet R M (↑(I ^ n) : Set R)

end AddCommMonoid
end Module
end
