public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_conj {X : Subgroup G} {g x : G} : x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

end L14324
end CFSG.Quasithin.H13
end
