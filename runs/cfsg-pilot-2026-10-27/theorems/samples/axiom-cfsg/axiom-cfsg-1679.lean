public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section LeviData

open CFSG.RankThree.OrthogonalInvolutions (fixSpace commSpace mem_fixSpace mem_commSpace)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_comap_eq_of_le_range (f : V →ₗ[K] V) {U : Submodule K V}
    (hU : U ≤ LinearMap.range f) :
    Module.finrank K (U.comap f) = Module.finrank K U + Module.finrank K (LinearMap.ker f) := by
  set g := f.domRestrict (U.comap f)
  have hrange : LinearMap.range g = U := by
    rw [LinearMap.range_domRestrict, Submodule.map_comap_eq, inf_eq_right.mpr hU]
  have hker : Module.finrank K (LinearMap.ker g) = Module.finrank K (LinearMap.ker f) := by
    have hle : LinearMap.ker f ≤ U.comap f := fun x hx => by
      rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]
      exact U.zero_mem
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker] at h
  exact h.symm

end LeviData
end CFSG.SeitzReduction.OmegaPilot
end
