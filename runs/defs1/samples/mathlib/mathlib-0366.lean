@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory ModuleCat Finset Pi

universe u

namespace TannakaDuality

namespace FiniteGroup

variable {k G : Type u} [CommRing k] [Group G]

variable [Finite G]

/-- For `v : X` and `G` a finite group, the `G`-equivariant linear map from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`. -/
@[simps]
def sumSMulInv [Fintype G] {X : FDRep k G} (v : X) : (G → k) →ₗ[k] X where
  toFun f := ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' _ _ := by simp [add_smul, sum_add_distrib]
  map_smul' _ _ := by simp [smul_sum, smul_smul]

end FiniteGroup
end TannakaDuality
end
end
