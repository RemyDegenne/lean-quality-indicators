public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff)

section Bar

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G}

theorem IsDih.bar {P : Subgroup G} (hP : IsDih P) (hPH : P ≤ H) : IsDih (bar H P) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hP
  obtain ⟨f⟩ := nonempty_mulEquiv_bar hPH (IsDih.isPGroup ⟨a, ha, ⟨e⟩⟩)
  exact ⟨a, ha, ⟨f.symm.trans e⟩⟩

end Bar
end CFSG.GH72
end
