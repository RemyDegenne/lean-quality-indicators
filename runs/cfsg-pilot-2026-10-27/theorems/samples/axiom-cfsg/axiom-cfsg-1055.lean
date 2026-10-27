public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped MatrixGroups Matrix

open CFSG.HardMathSupport.U4FF (SU4 twistHom)

open CFSG.LieType.Universal.Unitary (antidiag conjTr mem_SU)

open CFSG.LieType.BorelTits (unitaryInvolution_apply)

section Matrices

variable (k : Type) [Field k]

theorem finU4Z1_map {k' : Type} [Field k'] (φ : k →+* k') :
    Matrix.SpecialLinearGroup.map φ (finU4Z1 k) = finU4Z1 k' :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    exact finU4ZMat_map k φ)

end Matrices
end CFSG.LocalAnalysis.WeakClosure81
end
