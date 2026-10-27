namespace P2MW.S_CuspFormClass_isZeroAt_slash_ratCast

namespace ModularForm

namespace S06W2

p2m_open

open UpperHalfPlane OnePoint

p2m_open_scoped

section HeckeMatrices

def ratUpperTriangularGL (a b d : ℚ) (had : a * d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

end HeckeMatrices
end S06W2
end ModularForm
end P2MW.S_CuspFormClass_isZeroAt_slash_ratCast
