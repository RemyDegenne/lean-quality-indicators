public section

namespace CFSG.GroupTheory.AutomorphismAction

theorem eq_one_of_involutive_centralizing {E : Type*} [Group E] {p : ℕ} (hp : Odd p)
    (hexp : ∀ x : E, x ^ p = 1) (α : E ≃* E) (hinv : ∀ x, α (α x) = x)
    (hcenter : ∀ z ∈ Subgroup.center E, α z = z)
    (hquot : ∀ x, α x * x⁻¹ ∈ Subgroup.center E) :
    α = 1 := by
  ext y
  have hd := hquot y
  have h1 : α (α y * y⁻¹) = α y * y⁻¹ := hcenter _ hd
  have h2 : (α y * y⁻¹) ^ 2 = 1 := by
    have h3 : α (α y * y⁻¹) = y * α y⁻¹ := by simp [hinv]
    have h4 : y * (α y)⁻¹ = α y * y⁻¹ := by rw [← map_inv, ← h3, h1]
    have h5 : (α y * y⁻¹) * (α y * y⁻¹) = 1 := by
      calc (α y * y⁻¹) * (α y * y⁻¹) = (α y * y⁻¹) * (y * (α y)⁻¹) := by rw [h4]
        _ = 1 := by group
    simpa [pow_two] using h5
  obtain ⟨k, hk⟩ := hp
  have h6 : (α y * y⁻¹) = 1 := by
    have := hexp (α y * y⁻¹)
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at this
    exact this
  simpa [mul_inv_eq_one] using h6

end CFSG.GroupTheory.AutomorphismAction
end
