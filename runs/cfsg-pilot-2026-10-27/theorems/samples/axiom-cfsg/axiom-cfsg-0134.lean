public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup Equiv.Perm.OnCycleFactors

theorem degPerm_conj_cycle_ne {α : Type*} [Fintype α] [DecidableEq α] {t σ c : Perm α} {k : ℕ}
    (ht : t * t = 1) (htk : t.support.card = 2 * k) (hσ : σ * σ = t)
    (hc : c ∈ t.cycleFactorsFinset) : σ * c * σ⁻¹ ≠ c := by
  intro h
  have h2 := AhatData.card_support_eq_two_of_mem_cycleFactorsFinset ht htk hc
  obtain ⟨x, y, hxy, rfl⟩ := Equiv.Perm.card_support_eq_two.1 h2
  have hct := (mem_cycleFactorsFinset_iff.1 hc).2
  have htx : t x = y := by
    rw [← hct x (by rw [support_swap hxy]; simp), swap_apply_left]
  have hσσ : ∀ a, σ (σ a) = t a := fun a => by rw [← hσ, Perm.mul_apply]
  have h1 : σ x ≠ x := fun h' => hxy (by have := hσσ x; rwa [h', h', htx] at this)
  have h1' : σ x ≠ y := fun h' => hxy (σ.injective (by
    have := hσσ x
    rw [h', htx] at this
    rw [h', this]))
  have h3 : swap (σ x) (σ y) (σ x) = swap x y (σ x) := by rw [swap_apply_apply, h]
  rw [swap_apply_left, swap_apply_of_ne_of_ne h1 h1'] at h3
  exact hxy (σ.injective h3.symm)

end CFSG.OddStandard.Solomon75
end
