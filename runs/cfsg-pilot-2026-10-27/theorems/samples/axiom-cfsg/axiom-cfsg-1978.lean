public noncomputable section

namespace CFSG.StandardType.TwE6E4bScalarLine

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType.TwE6FixedA2SL3 CFSG.StandardType.TwE6FixedA2Type

open CFSG.StandardType.TableBExc.E6Three

open CFSG.StandardType.TwE6E4bFrame CFSG.StandardType.TwE6E4bFlag CFSG.StandardType.TwE6E4bTorus

open CFSG.StandardType.TwE6E4bNormalizers CFSG.StandardType.TwE6HyperplaneTypes

open CFSG.StandardType.E4bLift

open scoped MatrixGroups

local instance : NeZero Tag.E6.rank := ⟨by decide⟩

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem rootVec_mem_Vlong_of_mem_fixedA2E6 {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ fixedA2E6) :
    rootVec Tag.E6 L γ ∈ Vlong L := by
  rw [Vlong_eq_span_fixedA2E6]
  exact Submodule.subset_span ⟨γ, hγ, rfl⟩

end CFSG.StandardType.TwE6E4bScalarLine
end
