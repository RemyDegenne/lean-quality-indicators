public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

section Torus

variable {K : Type} [Field K] [CharP K 2]

set_option maxRecDepth 20000 in
theorem rootOp_yxy {α : Rt} (hα : IsRoot .E7 α) :
    e7Data.rootOp K (-α) * e7Data.rootOp K α * e7Data.rootOp K (-α) = e7Data.rootOp K (-α) := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply, rootOp_rootOp_neg hα, rootOp_neg_Pσ_one hα]

end Torus
end CFSG.RankThree.GF2n.Smith81.MinuscT
end
