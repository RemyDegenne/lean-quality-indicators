@[expose] public section

open Function

open scoped Pointwise

universe u v w x

namespace QuotientGroup

variable {G : Type u} [Group G] (N : Subgroup G) [nN : N.Normal] {H : Type v} [Group H]
  {M : Type x} [Monoid M]

local notation " Q " => G ⧸ N

variable (φ : G →* H)

open MonoidHom

section ThirdIsoThm

variable (M : Subgroup G) [nM : M.Normal]

variable (h : N ≤ M)

/-- The map from the third isomorphism theorem for groups: `(G / N) / (M / N) → G / M`. -/
@[to_additive /-- The map from the third isomorphism theorem for additive groups:
`(A / N) / (M / N) → A / M`. -/]
def quotientQuotientEquivQuotientAux : (G ⧸ N) ⧸ M.map (mk' N) →* G ⧸ M :=
  lift (M.map (mk' N)) (map N M (MonoidHom.id G) h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_ker, map_mk' N M (MonoidHom.id G) (by simpa) x]
      exact (QuotientGroup.eq_one_iff _).mpr hx)

end ThirdIsoThm
end QuotientGroup
end
