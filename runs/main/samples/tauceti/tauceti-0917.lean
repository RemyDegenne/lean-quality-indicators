public section

namespace TauCeti

open Finset Module

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w} {M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

section TorusCharacter

variable [Fintype κ]

theorem exists_torusCharacter_eq_of_sum_mul_eq_one {μ m : κ → ℤ} (hm : ∑ j, μ j * m j = 1)
    (u : Rˣ) : ∃ s : κ → Rˣ, torusCharacter s μ = u := by
  refine ⟨fun j => u ^ m j, ?_⟩
  rw [torusCharacter_def]
  calc ∏ j, (u ^ m j) ^ μ j = ∏ j, u ^ (m j * μ j) :=
        Finset.prod_congr rfl fun j _ => (zpow_mul u (m j) (μ j)).symm
    _ = u ^ ∑ j, m j * μ j := Finset.prod_zpow_eq_zpow_sum _ u _
    _ = u := by
        rw [Finset.sum_congr rfl fun j _ => mul_comm (m j) (μ j), hm, zpow_one]

end TorusCharacter
end TauCeti
end
