public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

open scoped commutatorElement

section L3Transport

open CFSG.Quasithin.L3Lat

variable {X : Type*} [Group X]

theorem mem_of_normalizes_equiv (e : X ≃* Γ) (D : Subgroup X) (hD : Nat.card D = 8) (x : X)
    (hx : ∀ d ∈ D, x * d * x⁻¹ ∈ D) : x ∈ D := by
  let D' : Subgroup Γ := D.map e.toMonoidHom
  have hD' : Nat.card D' = 8 := by
    rw [← hD]
    exact Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).symm.toEquiv
  have h1 : e x ∈ D' := by
    apply mem_of_normalizes D' hD'
    intro d hd
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hd
    exact Subgroup.mem_map.mpr ⟨x * y * x⁻¹, hx y hy, by simp⟩
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
  have : y = x := e.injective hyx
  rw [← this]
  exact hy

end L3Transport
end CFSG.Quasithin
end
