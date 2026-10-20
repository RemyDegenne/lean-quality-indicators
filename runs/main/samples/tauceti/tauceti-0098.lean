public section

namespace TauCeti

open LieModule Module

universe v

section Projection

variable {K : Type*} [CommRing K]

variable {L : Type*} [LieRing L]

variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M]

theorem exists_isCompl_of_equivariant_projection {N : LieSubmodule K L M} {ψ : M →ₗ[K] M}
    (hψmem : ∀ m, ψ m ∈ N) (hψid : ∀ n ∈ N, ψ n = n)
    (hψlie : ∀ (x : L) (m : M), ψ ⁅x, m⁆ = ⁅x, ψ m⁆) :
    ∃ N' : LieSubmodule K L M, IsCompl N N' := by
  -- `ψ` corestricted to `N` is a Lie module hom, and a projection in Mathlib's sense.
  let g : M →ₗ⁅K,L⁆ M := { __ := ψ, map_lie' := fun {x m} ↦ hψlie x m }
  let f : M →ₗ⁅K,L⁆ N := LieModuleHom.codRestrict N g hψmem
  refine ⟨f.ker, ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule, LieModuleHom.ker_toSubmodule]
  exact LinearMap.isCompl_of_proj fun n ↦ Subtype.ext (hψid n n.2)

end Projection
end TauCeti
end
