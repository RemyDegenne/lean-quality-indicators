public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.Visible Module
  Matrix

theorem latHom_negOneO (x : LL) : latHom negOneO x = -x := by
  apply Subtype.ext
  apply ratVec_injective
  rw [ratVec_latHom, mat_negOneO, vecMul_neg, vecMul_one]
  exact (ScalarKernel.ratVec_neg _).symm

end CFSG.Monster.B.Short
end
