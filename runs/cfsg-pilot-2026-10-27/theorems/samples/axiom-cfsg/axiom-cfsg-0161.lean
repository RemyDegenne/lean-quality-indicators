public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open Equiv Equiv.Perm

theorem isSolvable_of_index_le_four {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : Group.IsSolvable ↥H) (hidx : H.index ≤ 4) : Group.IsSolvable G := by
  let f := MulAction.toPermHom G (G ⧸ H)
  have hperm : Group.IsSolvable (Perm (G ⧸ H)) := Equiv.Perm.isSolvable (by exact hidx)
  have hker : f.ker ≤ H := by
    rw [← Subgroup.normalCore_eq_ker]
    exact Subgroup.normalCore_le H
  have : Group.IsSolvable ↥f.ker :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hker)
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
end
