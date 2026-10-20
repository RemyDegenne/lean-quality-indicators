namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace B2SubV

variable (q M' : ℕ) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))

scoped instance algK : Algebra ↥k₀ (FB q M') :=
  ((algebraMap (AlgebraicClosure ℚ) (FB q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

def Lbar : IntermediateField ↥k₀ (FB q M') := (ιL q M' k₀).fieldRange

end B2SubV
end
end P2MW.S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart
