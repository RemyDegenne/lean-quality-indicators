public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin

namespace W5

theorem mem_normalizer_iff_map_eq {X : Type*} [Group X] {A : Subgroup X} {g : X} :
    g ∈ Subgroup.normalizer (A : Set X) ↔ A.map (MulAut.conj g).toMonoidHom = A := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hg _).2 (by simpa [mul_assoc] using hx), ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        simpa using h1
      rwa [← this]

end W5
end CFSG.Quasithin.He9
end
