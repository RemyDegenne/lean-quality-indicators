public section

namespace TauCeti

open Topology

universe u v

variable (R : Type u) [CommRing R] (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

namespace completedGroupAlgebra

variable {R Γ}

variable (R Γ)

/-- All coefficients of all projections, as one additive map into a product of
copies of `R`. The topology of the completed group algebra is the one induced along this map:
the coarsest topology making every coefficient of every projection continuous. -/
noncomputable def coeffFamily :
    completedGroupAlgebra R Γ →+ ∀ U : OpenNormalSubgroup Γ, Γ ⧸ U.toSubgroup → R where
  toFun x U := ⇑(proj R Γ U x).coeff
  map_zero' := funext fun U ↦ by simp
  map_add' x y := funext fun U ↦ by
    simp only [Pi.add_apply, map_add, MonoidAlgebra.coeff_add, Finsupp.coe_add]

end completedGroupAlgebra
end TauCeti
end
