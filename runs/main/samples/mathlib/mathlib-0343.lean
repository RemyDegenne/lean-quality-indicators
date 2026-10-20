@[expose] public section

open Function

open scoped Int

variable {G G' : Type*} [Group G] [Group G']

variable {A : Type*} [AddGroup A]

namespace Subgroup

variable (H K : Subgroup G)

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

@[to_additive (attr := simp)]
theorem map_one_eq_bot : K.map (1 : G →* N) = ⊥ :=
  eq_bot_iff.mpr <| by
    rintro x ⟨y, _, rfl⟩
    simp

end Subgroup
end
