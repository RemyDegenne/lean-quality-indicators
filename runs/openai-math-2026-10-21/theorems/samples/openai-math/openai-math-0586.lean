namespace OAI

noncomputable section

namespace CircleSampling

universe uι

open MeasureTheory

open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

open MeasureTheory Filter Set Submodule

open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set

open scoped ComplexInnerProductSpace

open MeasureTheory Filter Set

open Set

open scoped ComplexInnerProductSpace

open Set

open scoped ComplexInnerProductSpace

open MeasureTheory Set Filter Topology

open scoped BigOperators ComplexConjugate

open MeasureTheory Set Filter

open scoped BigOperators ENNReal

open Filter Set

open scoped Topology

open Filter Set

open scoped Topology

open Set MeasureTheory

open scoped BigOperators ENNReal Classical

open Filter Set

open scoped Topology

open Set MeasureTheory

open scoped ENNReal Classical

open Filter

open scoped Topology

open Set Filter

open scoped Topology

open Set Topology

open scoped BigOperators

open scoped BigOperators

open Set

open Set

open Set

open Set MeasureTheory Filter

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Set Filter

open scoped ENNReal Topology

open MeasureTheory Set

open MeasureTheory Filter Set

open scoped Topology BoundedContinuousFunction

open MeasureTheory Set Filter Topology TopologicalSpace

open MeasureTheory Set

open scoped ENNReal BigOperators Classical

open MeasureTheory Set

open scoped BigOperators ENNReal Classical

open MeasureTheory Set

open scoped ENNReal

open MeasureTheory Set

open scoped ENNReal NNReal

open MeasureTheory Set Filter

open scoped BigOperators ENNReal Topology

open Set MeasureTheory Topology

open scoped symmDiff

open MeasureTheory Set

open scoped ENNReal BigOperators

open MeasureTheory Set

open scoped ENNReal

open MeasureTheory Set

open scoped BigOperators ENNReal

open MeasureTheory Set

open scoped ENNReal NNReal BigOperators

open MeasureTheory Filter Set

open scoped Topology ENNReal BigOperators

section

open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight

open Set Filter MeasureTheory

open scoped Topology BigOperators ENNReal

lemma smoothDrop_coboundary (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    smoothDrop j i x-integerDrop j i x=smoothCorrection j i (x+modelAngle)-smoothCorrection j i x := by
  have hp := phase_orbit (blocks.equiv ⟨j,i⟩) 1
  simp only [one_smul,Int.cast_one,one_mul] at hp
  unfold smoothDrop integerDrop smoothCorrection floorTerm
  rw [model_beta]
  simp only [Int.cast_one,one_mul]
  change roundedDrop _ _ _ _ - dropSize j * (⌊CircleRounding.repr _+_⌋:ℝ)=_
  rw [roundedDrop_coboundary,nsmul_add,hp]

end
end CircleSampling
end
end OAI
