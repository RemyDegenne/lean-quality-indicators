@[expose] public section

namespace DiscreteTiling

open Function

open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable (G X) in
/-- A `Prototile G X` describes a tile in `X`, copies of which under elements of `G` may be used in
tilings. Two copies related by an element of `symmetries` are considered the same; two copies not so
related, even if they have the same points, are considered distinct. -/
@[ext] structure Prototile where
  /-- The points in the prototile. Use the coercion to `Set X`, or `∈` on the `Prototile`, rather
      than using `carrier` directly. The coercion cannot use `SetLike` because it does not satisfy
      `coe_injective`. -/
  carrier : Set X
  /-- The group elements considered to be symmetries of the prototile. -/
  symmetries : Subgroup (MulAction.stabilizer G carrier)

end DiscreteTiling
end
