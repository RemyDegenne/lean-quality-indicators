public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration

open scoped Matrix

section Weyl

theorem w0_mul_z0 : e8PhiFourWeyl * z0 = z0 * e8PhiFourWeyl := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := V8) fun v => ?_
  have h : M0 * Mz = Mz * M0 := by
    rw [M0, Mz, ← toMat_lmul, ← toMat_lmul]
    exact congrArg (toMat Tag.E8.rank) (by decide +kernel)
  rw [mul_smul, mul_smul, z0_smul, w0_smul, w0_smul, z0_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

end Weyl
end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
end
