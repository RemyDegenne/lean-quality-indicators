@[expose] public section

universe u v w

namespace Module

section Pi

variable (R : Type u) {ι : Type w} (M : ι → Type v) [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

@[simp]
theorem isKilledByIdealPower_pi_iff_of_finite [_root_.Finite ι] (I : Ideal R) :
    IsKilledByIdealPower R (Π i, M i) I ↔ ∀ i, IsKilledByIdealPower R (M i) I := by
  rw [isKilledByIdealPower_pi_iff R M I]
  constructor
  · rintro ⟨n, hn⟩ i
    exact ⟨n, hn i⟩
  · intro h
    classical
    choose n hn using h
    obtain ⟨m, hm⟩ := Finite.exists_le n
    exact ⟨m, fun i ↦ isTorsionBySet_ideal_pow_of_le R (M i) I (hm i) (hn i)⟩

end Pi
end Module
end
