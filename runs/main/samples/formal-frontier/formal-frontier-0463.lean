@[expose] public section

universe u v w

namespace Module

section Pi

variable (R : Type u) {ι : Type w} (M : ι → Type v) [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem isKilledByIdealPower_pi_iff (I : Ideal R) :
    IsKilledByIdealPower R (Π i, M i) I ↔
      ∃ n : ℕ, ∀ i, IsTorsionBySet R (M i) (↑(I ^ n) : Set R) := by
  rw [isKilledByIdealPower_iff_exists_pow_le_annihilator, Module.annihilator_pi]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun i ↦ ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    exact (le_iInf_iff.mp hn) i
  · rintro ⟨n, hn⟩
    refine ⟨n, le_iInf fun i ↦ ?_⟩
    exact (Module.isTorsionBySet_iff_subset_annihilator R (M i)).mp (hn i)

end Pi
end Module
end
