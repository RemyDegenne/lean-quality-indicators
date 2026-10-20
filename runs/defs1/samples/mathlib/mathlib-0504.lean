@[expose] public section

open Function

open scoped Int

variable {G G' : Type*} [Group G] [Group G']

variable {A : Type*} [AddGroup A]

namespace Subgroup

variable (H K : Subgroup G)

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

/-- The image of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive
      /-- The image of an `AddSubgroup` along an `AddMonoid` homomorphism
      is an `AddSubgroup`. -/]
def map (f : G →* N) (H : Subgroup G) : Subgroup N :=
  { H.toSubmonoid.map f with
    carrier := f '' H
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ }

end Subgroup
end
