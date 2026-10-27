public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem pCore_ne_bot_of {H X : Subgroup G} (hXH : X ≤ H)
    (hXn : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hX2 : IsPGroup 2 X) (hX1 : X ≠ ⊥) :
    CFSG.pCore 2 H ≠ ⊥ := by
  intro h0
  apply hX1
  have hle : X.subgroupOf H ≤ CFSG.pCore 2 H :=
    le_sSup ⟨⟨fun n hn k => by
      rw [mem_subgroupOf] at hn ⊢
      exact hXn k k.2 n hn⟩, hX2.comap_of_injective H.subtype H.subtype_injective⟩
  rw [h0] at hle
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H := by rw [mem_subgroupOf]; exact hx
  have h1 := hle this
  rw [mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

end Setting
end CFSG.LargeExtraspecial
end
