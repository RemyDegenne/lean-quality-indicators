public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin

variable {G : Type} [Group G] {X : Subgroup G} {Q : Type*} [Group Q]

theorem mem_imgIn {Ψ : ↥X →* Q} {Y : Subgroup G} {q : Q} :
    q ∈ imgIn Ψ Y ↔ ∃ (x : G) (hx : x ∈ X), x ∈ Y ∧ Ψ ⟨x, hx⟩ = q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, y.2, hy, rfl⟩
  · rintro ⟨x, hx, hxY, rfl⟩
    exact ⟨⟨x, hx⟩, hxY, rfl⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
end
