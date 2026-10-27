public section

namespace CFSG.Quasithin.H13.Seven

open MulAction Subgroup

theorem conj_pow_odd {G : Type*} [Group G] {y g : G} (hg : g * y * g⁻¹ = y⁻¹) {o : ℕ}
    (ho : Odd o) : g ^ o * y * (g ^ o)⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := ho
  have h1 : g * y⁻¹ * g⁻¹ = y := by
    have := congrArg (fun z => z⁻¹) hg
    simpa [mul_assoc] using this
  have h2 : g ^ 2 * y = y * g ^ 2 := by
    have : g * (g * y * g⁻¹) * g⁻¹ = g * y⁻¹ * g⁻¹ := by rw [hg]
    rw [h1] at this
    rw [pow_two]
    calc g * g * y = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by group
      _ = y * (g * g) := by rw [this]
  have h3 : Commute (g ^ 2) y := h2
  have h4 : Commute ((g ^ 2) ^ k) y⁻¹ := (h3.pow_left k).inv_right
  calc g ^ (2 * k + 1) * y * (g ^ (2 * k + 1))⁻¹
      = (g ^ 2) ^ k * (g * y * g⁻¹) * ((g ^ 2) ^ k)⁻¹ := by group
    _ = y⁻¹ := by rw [hg, h4.eq]; group

end CFSG.Quasithin.H13.Seven
end
