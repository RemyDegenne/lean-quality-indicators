namespace OAI

namespace BorsukNine

open scoped BigOperators

lemma simplexProjection_fixed {ι : Type*} [Fintype ι] {x : EuclideanSpace ℝ ι}
    (hx : coordinateSum x = 1) : simplexProjection x = x := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,hx,one_smul,sub_add_cancel]

end BorsukNine
end OAI
