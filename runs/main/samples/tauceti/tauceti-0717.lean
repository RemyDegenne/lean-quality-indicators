public section

noncomputable section

open Topology unitInterval

open scoped Topology.Homotopy

namespace TauCeti

universe u

variable (G : Type u) [Group G]

variable {G}

theorem classifyingSpaceFundamentalGroupMulEquiv_apply_mk_eq
    {γ : Path (classifyingSpaceBasepoint G) (classifyingSpaceBasepoint G)}
    {Γ : C(I, universalGSpace G)} {g : G} (hΓ : classifyingSpaceProj G ∘ Γ = γ)
    (hΓ₀ : Γ 0 = universalGSpaceBasepoint G)
    (hΓ₁ : Γ 1 = (indexedJoin fun _ : ℕ => G).vertex ⟨0, g⁻¹⟩) :
    classifyingSpaceFundamentalGroupMulEquiv G (.of (.mk γ)) = g :=
  classifyingSpaceFundamentalGroupMulEquiv_apply_eq_iff.mpr <| by
    rw [IsCoveringMap.monodromy_eq_apply_one _ hΓ hΓ₀, hΓ₁]

end TauCeti
end
end
