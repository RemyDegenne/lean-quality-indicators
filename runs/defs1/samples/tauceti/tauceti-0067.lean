public section

open CategoryTheory

open scoped Pointwise

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [hN : N.Normal]

section Ring

variable [Ring k]

/-- The **inertia group** of `A : FDRep k N`, for `N` a normal subgroup of `G`: the elements of
`G` whose conjugate representation `{}^g A` is isomorphic to `A`, i.e. the stabilizer of the
isomorphism class of `A` under `conjNormalFDRepSkeletonMulAction`.

See `TauCeti.mem_inertia_iff` for the description as `{g | {}^g A ≅ A}`, and
`TauCeti.stabilizer_le_inertia` for the comparison with the stabilizer of `A` itself. -/
noncomputable def inertia (A : FDRep k N) : Subgroup G :=
  MulAction.stabilizer G (toSkeleton A)

end Ring
end TauCeti
end
