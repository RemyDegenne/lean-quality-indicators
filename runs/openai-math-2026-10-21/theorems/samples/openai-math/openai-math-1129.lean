namespace OAI

section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma coordinateReflection_coordinatePermute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (z : Torus) :
    torusCoordinatePermute e (coordinateReflection i z)=
      coordinateReflection (e.symm i) (torusCoordinatePermute e z) := by
  ext j
  simp only [torusCoordinatePermute_apply,coordinateReflection_apply]
  simp only [show (j=e.symm i)↔e j=i from Equiv.eq_symm_apply e]

end CubicTorus
end
end
end OAI
