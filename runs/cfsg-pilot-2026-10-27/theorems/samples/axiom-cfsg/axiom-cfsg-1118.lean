public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.CosetTable AS62.Sem

namespace AS62

variable {G : Type} [Group G] [Finite G]

namespace Gens

variable {S : Setting G} {H : Subgroup G} (g : Gens S H)

omit [Finite G] in
theorem Φ10_surjective {y : G} (hy : g.IsY y) : Function.Surjective (g.Φ10 hy) := by
  intro m
  have hle : g.M0 y ≤ (g.Φ10 hy).range.map (g.M0 y).subtype :=
    (closure_le _).mpr (by
      rintro _ ⟨i, rfl⟩
      exact ⟨g.Φ10 hy (PresentedGroup.of i), ⟨_, rfl⟩, g.Φ10_of hy i⟩)
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hle m.2
  exact ⟨w, Subtype.ext hw⟩

end Gens
end AS62
end CFSG.LargeExtraspecial
end
