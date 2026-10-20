public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.groupCohomology ContCohomology

variable {K : Type} [Field K]

section Invariant

variable (K) [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : NormalLayer (AbsoluteGaloisGroup K))

@[simp]
theorem layerInv_cohomologyRes {small big : NormalLayer (AbsoluteGaloisGroup K)}
    (T : LayerRestriction small big) (x : big.H (unitsFormation K) 2) :
    layerInv K small (T.cohomologyRes (unitsFormation K) 2 x) =
      T.relativeDegree • layerInv K big x := by
  rw [layerInv_apply, NormalLayer.explicitInfl2_cohomologyRes,
    subgroupInvMap_explicitMap2_subgroupInclusion,
    LayerRestriction.relativeDegree_def, layerInv_apply]

end Invariant
end TauCeti.ClassFieldTheory
end
end
