namespace OAI

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem slopeAxes_apply (s : ℝ) (i : Fin 2) : slopeAxes s i = slopeAxisVectors s i := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

end LipschitzHilbert
end
end OAI
