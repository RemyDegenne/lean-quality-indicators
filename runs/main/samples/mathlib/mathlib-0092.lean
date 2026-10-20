@[expose] public section

open scoped Pointwise

namespace Subgroup

open Function

variable {G G' : Type*} [Group G] [Group G'] (H K L : Subgroup G)

variable {H K L}

variable (H K L)

variable {H K}

variable (H K) {f : G →* G'}

variable {H K L}

@[to_additive ]
lemma relIndex_comap_ne_zero (f : G →* G') {J K : Subgroup G'} (hJK : J.relIndex K ≠ 0) :
    (J.comap f).relIndex (K.comap f) ≠ 0 := by
  rw [relIndex_comap]
  exact fun h ↦ hJK <| relIndex_eq_zero_of_le_right (map_comap_le _ _) h

end Subgroup
end
