namespace OAI

open MeasureTheory Set

open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

open MeasureTheory Set Filter

open scoped ENNReal NNReal

open MeasureTheory Set Filter

open scoped ENNReal NNReal

namespace Coulomb

lemma H1Vector.cubeState_memLp {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    MemLp (cubeState ψ) 2 (Measure.pi fun _ : Fin n => spinCubeMeasure b) :=
  (ψ.spinCube_memLp b).comp_measurePreserving (spinCubeEquiv_measurePreserving n b)

end Coulomb
end OAI
